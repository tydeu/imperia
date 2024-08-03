
/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Imperia.Do.Basic

open Lean Parser

namespace Imperia

-- μdoNested
macro_rules
| `(μdo% μdo $x:doSeq $xs*) => do
  mkMDoAndThen (← withRef x ``(Cont.block μdo $x)) xs

-- doNested
macro_rules
| `(μdo% do $x:doSeq $xs*) => do
  mkMDoAndThen (← mkMDoOfSeq x) xs

-- doExpr
macro_rules
| `(μdo% $x:term $xs:doElem*) =>
  mkMDoTerm x fun x => mkMDoAndThen x xs

-- doLet
macro_rules
| `(μdo% let%$tk $[mut%$mutTk?]? $d:letDecl $xs:doElem*) => withRef tk do
  if let some tk := mutTk? then
    Macro.throwErrorAt tk "`mut` has not been implemented for `μdo`"
  let body ← mkMDoOfElems xs
  mkMDoTerm d fun d => `(let $d:letDecl; $body)

-- doLetElse
macro_rules
| `(μdo% let%$tk $[mut%$mutTk?]? $pat := $v | $e:doSeq $xs:doElem*) => withRef tk do
  if let some tk := mutTk? then
    Macro.throwErrorAt tk "`mut` has not been implemented for `μdo`"
  let e ← mkMDoOfSeq e
  let body ← mkMDoOfElems xs
  mkMDoTerm v fun v => `(if let $pat := $v then $body else $e)

-- doLetArrow
macro_rules
| `(μdo% let%$letTk $[mut%$mutTk?]? $decl $xs:doElem*) => withRef letTk do
  if let some tk := mutTk? then
    Macro.throwErrorAt tk "`mut` has not been implemented for `μdo`"
  match decl with
  | `(Term.doIdDecl|$id $[: $ty?]? ←%$bindTk $v) =>
    let body ← mkMDoOfElems xs
    mkMDoBind bindTk (← mkMDoOfElem v) `(fun $id $[: $ty?]? => $body)
  | `(Term.doPatDecl|$pat ←%$bindTk $v $[| $e?]?) => do
    let patAlt ← `(Term.matchAltExpr| | $pat => $(← mkMDoOfElems xs))
    let alts ← id do
      if let some e := e? then
        let eAlt ← withRef e `(Term.matchAltExpr| | _ => μdo% $(← expandDoSeq e)*)
        return #[patAlt, eAlt]
      else
        return #[patAlt]
    mkMDoBind bindTk (← mkMDoOfElem v) `(fun $alts:matchAlt*)
  | x => Macro.throwErrorAt x "ill-formed let declaration"

-- doMatch
macro_rules
| `(μdo% $stx:doMatch) => do
  let `(Term.doMatch|match%$tk $(generalizing?)? $(motive?)? $discrs,* with $alts:matchAlt*) := stx
    | Macro.throwErrorAt stx "ill-formed `do` match syntax"
  withRef tk do
  let alts ← alts.mapM mkMDoMatchAlt
  if let some motive := motive? then
    let (_, lifts) ← expandLiftMethod motive
    unless lifts.isEmpty do
      Macro.throwErrorAt motive "cannot lift `(<- ...)` over motive"
  mkMDoTerms discrs.getElems fun discrs =>
  `(match $(generalizing?)? $(motive?)? $discrs,* with $alts:matchAlt*)

def mkMDoIf (c : TSyntax ``Term.doIfCond) (t e : Term) : MacroM Term := do
  match c with
  | `(Term.doIfCond|let%$letTk $pat := $c) =>
    mkMDoTerm c fun c => `(if let%$letTk $pat := $c then $t else $e)
  | `(Term.doIfCond|let $pat ←%$bindTk $c) =>
    mkMDoTerm c fun c => mkMDoBind bindTk c `(fun | $pat => $t | _ => $e)
  | `(Term.doIfCond|$h :%$tk $c) =>
    mkMDoTerm c fun c => `(if $h :%$tk $c then $t else $e)
  | `(Term.doIfCond|$c:term) =>
    mkMDoTerm c fun c => `(if $c then $t else $e)
  | c => Macro.throwErrorAt c "ill-formed do `if` condition"

-- doIf
macro_rules
| `(μdo% if $c:doIfCond then $t $[else if $ecs:doIfCond then $ets]* $[else $e?]? $xs*) => do
  if h : xs.size > 0 then
    mkMDoJmp xs h fun jmp => do
      let e ← if let some e := e? then mkMDoSeqThenJmp e jmp else pure jmp
      let e ← (ecs.zip ets).foldrM (init := e) fun (c, t) e => do
        mkMDoIf c (← mkMDoSeqThenJmp t jmp) e
      mkMDoIf c (← mkMDoSeqThenJmp t jmp) e
  else
    let e ← if let some e := e? then mkMDoOfSeq e else ``(nop)
    let e ← (ecs.zip ets).foldrM (init := e) fun (c, t) e => do
      mkMDoIf c (← mkMDoOfSeq t) e
    mkMDoIf c (← mkMDoOfSeq t) e

-- doUnless
macro_rules
| `(μdo% unless $c do $x:doSeq $xs*) => do
  if h : xs.size > 0 then
    mkMDoJmp xs h fun jmp => do
      let x ← mkMDoSeqThenJmp x jmp
      mkMDoTerm c fun c => `(if $c then $jmp else $x)
  else
    let x ← mkMDoOfSeq x
    mkMDoTerm c fun c => `(if $c then nop else $x)

-- doReturn
macro_rules
| `(μdo% return%$tk $(v?)? $xs*) => withRef tk do
  if xs.size > 0 then
    Macro.throwErrorAt tk "return must be the last element in a `do` sequence"
  else if let some v := v? then
    mkMDoTerm v fun v => ``(ret $v)
  else
    ``(halt)

-- doRaise
macro_rules
| `(μdo% raise%$tk $(v?)? $xs*) => withRef tk do
  if xs.size > 0 then
    Macro.throwErrorAt tk "raise must be the last element in a `do` sequence"
  else if let some v := v? then
    mkMDoTerm v fun v => ``(Throw.throw $v)
  else
    ``(Throw.throw ())

-- doTry
macro_rules
| `(μdo% try%$tk $x:doSeq $catches* $[finally $f?]? $xs*) => withRef tk do
  let x ← mkMDoOfSeq x
  let x ← catches.foldlM (init := x) fun x c => withRef c do
    match c with
    | `(Term.doCatch|catch $e $[: $ty?]? => $c) =>
      let c ← mkMDoOfSeq c
      if let some ty := ty? then
        ``(HTryCatch.tryCatchThe $ty $x fun $e => $c)
      else
        ``(HTryCatch.tryCatchOut $x fun $e => $c)
    | `(Term.doCatchMatch|catch $[$alts:matchAlt]*) =>
      let alts ← alts.mapM mkMDoMatchAlt
      ``(HTryCatch.tryCatchOut $x fun $[$alts:matchAlt]*)
    | c => Macro.throwErrorAt c ""
  let x ←
    if let some f := f? then
      withRef f ``(TryFinally.tryFinally $x μdo% $(← expandDoSeq f)*)
    else
      pure x
  mkMDoAndThen x xs
