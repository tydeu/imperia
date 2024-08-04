
/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Imperia.Do.Basic

open Lean Parser

namespace Imperia

-- μdoNested
macro_rules | `(μdo% $x:μdoNested $xs*) => do
  let `(μdoNested|μdo $s:doSeq) := x
    | Macro.throwErrorAt x "ill-formed nested `μdo` syntax"
  withRef x.raw[0] do
  let b ← ``(Cont.block μdo $s)
  mkMDoAndThen b xs

-- doNested
macro_rules | `(μdo% $x:doNested $xs*) => do
  let `(Term.doNested|do $x:doSeq) := x
    | Macro.throwErrorAt x "ill-formed nested `do` syntax"
  mkMDoAndThen (← mkMDoOfSeq x) xs

-- doExpr
macro_rules | `(μdo% $x:doExpr $xs*) => do
  let `(Term.doExpr|$x:term) := x
    | Macro.throwErrorAt x "ill-formed `do` expression"
  mkMDoTerm x fun x => mkMDoAndThen x xs

-- doLet
macro_rules | `(μdo% $x:doLet $xs*) => do
  let `(Term.doLet|let%$tk $[mut%$mutTk?]? $d:letDecl) := x
    | Macro.throwErrorAt x "ill-formed `do` let syntax"
  withRef tk do
  if let some tk := mutTk? then
    Macro.throwErrorAt tk "`mut` has not been implemented for `μdo`"
  let body ← mkMDoOfElems xs
  mkMDoTerm d fun d => `(let $d:letDecl; $body)

-- doLetElse
macro_rules | `(μdo% $x:doLetElse $xs*) => do
  let `(Term.doLetElse|let%$tk $[mut%$mutTk?]? $pat := $v | $e:doSeq) := x
    | Macro.throwErrorAt x "ill-formed `do` let syntax"
  withRef tk do
  if let some tk := mutTk? then
    Macro.throwErrorAt tk "`mut` has not been implemented for `μdo`"
  let e ← mkMDoOfSeq e
  let body ← mkMDoOfElems xs
  mkMDoTerm v fun v => `(if let $pat := $v then $body else $e)

-- doLetArrow
macro_rules | `(μdo% $x:doLetArrow $xs*) => do
  let `(Term.doLetArrow|let%$letTk $[mut%$mutTk?]? $decl) := x
    | Macro.throwErrorAt x "ill-formed `do` let syntax"
  withRef letTk do
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
macro_rules | `(μdo% $stx:doMatch $xs*) => do
  let `(Term.doMatch|match%$tk $(generalizing?)? $(motive?)? $discrs,* with $alts:matchAlt*) := stx
    | Macro.throwErrorAt stx "ill-formed `do` match syntax"
  withRef tk do
  if let some motive := motive? then
    let (_, lifts) ← expandLiftMethod motive
    unless lifts.isEmpty do
      Macro.throwErrorAt motive "cannot lift `(<- ...)` over motive"
  mkMDoJmp xs fun jmp => do
  let alts ← mkMDoMatchAlts alts jmp
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
  | c => Macro.throwErrorAt c "ill-formed `do` if condition"

-- doIf
macro_rules | `(μdo% $x:doIf $xs*) => do
  let `(Term.doIf|if%$tk $c:doIfCond then $t $[else if $ecs:doIfCond then $ets]* $[else $e?]?) := x
    | Macro.throwErrorAt x "ill-formed `do` if syntax"
  withRef tk do
  mkMDoJmp xs fun jmp => do
  let e ← if let some e := e? then mkMDoSeqJmp e jmp else jmp.mkTerm
  let e ← (ecs.zip ets).foldrM (init := e) fun (c, t) e => do
    mkMDoIf c (← mkMDoSeqJmp t jmp) e
  mkMDoIf c (← mkMDoSeqJmp t jmp) e

-- doUnless
macro_rules | `(μdo% $x:doUnless $xs*) => do
  let `(Term.doUnless|unless%$tk $c do $x:doSeq) := x
    | Macro.throwErrorAt x "ill-formed `do` unless syntax"
  withRef tk do
  mkMDoJmp xs fun jmp => do
  let x ← mkMDoSeqJmp x jmp
  let jmp ← jmp.mkTerm
  mkMDoTerm c fun c => `(if $c then $jmp else $x)

-- doReturn
macro_rules | `(μdo% $x:doReturn $xs*) => do
  let `(Term.doReturn|return%$tk $(v?)?) := x
    | Macro.throwErrorAt x "ill-formed `do` return syntax"
  withRef tk do
  if xs.size > 0 then
    Macro.throwErrorAt tk "return must be the last element in a `do` sequence"
  else if let some v := v? then
    mkMDoTerm v fun v => ``(ret $v)
  else
    ``(halt)

-- doRaise
macro_rules | `(μdo% $x:doRaise $xs*) => do
  let `(doRaise|raise%$tk $(v?)?) := x
    | Macro.throwErrorAt x "ill-formed `do` raise syntax"
  withRef tk do
  if xs.size > 0 then
    Macro.throwErrorAt tk "raise must be the last element in a `do` sequence"
  else if let some v := v? then
    mkMDoTerm v fun v => ``(Throw.throw $v)
  else
    ``(Throw.throw ())

-- doTry
macro_rules | `(μdo% $x:doTry $xs*) => do
  let `(Term.doTry|try%$tk $x:doSeq $catches* $[$f?:doFinally]?) := x
    | Macro.throwErrorAt x "ill-formed `do` try syntax"
  withRef tk do
  mkMDoJmp xs fun jmp => do
  let x ← mkMDoSeqJmp x jmp
  let x ← catches.foldlM (init := x) fun x c => do
    match c with
    | `(Term.doCatch|catch%$tk $e $[: $ty?]? => $c) => withRef tk do
      let c ← mkMDoSeqJmp c jmp
      if let some ty := ty? then
        ``(HTryCatch.tryCatchThe $ty $x fun $e => $c)
      else
        ``(HTryCatch.tryCatchOut $x fun $e => $c)
    | `(Term.doCatchMatch|catch%$tk $[$alts:matchAlt]*) => withRef tk do
      let alts ← mkMDoMatchAlts alts jmp
      ``(HTryCatch.tryCatchOut $x fun $[$alts:matchAlt]*)
    | c => Macro.throwErrorAt c "ill-formed `do` catch syntax"
  if let some f := f? then
    let `(Term.doFinally|finally%$tk $f) := f
      | Macro.throwErrorAt f "ill-formed `do` finally syntax"
    let f ← mkMDoSeqJmp f jmp
    withRef tk ``(TryFinally.tryFinally $x $f)
  else
    return x
