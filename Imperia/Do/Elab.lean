/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Imperia.Do.Basic
import Imperia.Iter

open Lean Elab Term.Do Parser

namespace Imperia

syntax (name := μdoScopes) "μdo_scopes%" : doElem

@[μdo_elab μdoScopes]
def elabMDoScopes : MDoElab := fun x xs expectedType? => do
  let scopes ← getMDoScopes
  let scopes := flip MessageData.joinSep "\n" <| scopes.stack.map fun scope =>
    m!"· mutable vars: {scope.vars.map (·.name)}"
  logInfoAt x m!"μdo scopes:{indentD scopes}"
  elabMDoElems xs expectedType?

@[μdo_elab μdoGoto]
def elabMDoGoto : MDoElab := adaptMDoMacroElab fun x _ => do
  let `(μdoGoto|μdo_goto% $x) := x
    | throwAt x "ill-formed `μdo_goto%` syntax"
  applyMDoVars x

@[μdo_elab μdoNested]
def elabΜdoNested := adaptMDoMacro fun x xs => do
  let `(μdoNested|μdo $s:doSeq) := x
    | throwAt x "ill-formed nested `μdo` syntax"
  withRef x.raw[0] do
  let s ← mkMDoOfSeq s
  let b ← ``(Cont.block $s)
  mkMDoAndThen b xs

@[μdo_elab doNested]
def elabDoNested := adaptMDoMacro fun x xs => do
  let `(Term.doNested|do $x:doSeq) := x
    | throwAt x "ill-formed nested `do` syntax"
  mkMDoAndThen (← mkMDoOfSeq x) xs

@[μdo_elab doExpr]
def elabDoExpr := adaptMDoMacro fun x xs => do
  let `(Term.doExpr|$x:term) := x
    | throwAt x "ill-formed `do` expression"
  mkMDoTerm x fun x => mkMDoAndThen x xs

@[μdo_elab doLet]
def elabDoLet := adaptMDoMacroElab fun x xs => do
  let `(Term.doLet|let%$tk $[mut%$mutTk?]? $decl:letDecl) := x
    | throwAt x "ill-formed `do` let syntax"
  withRef tk do
  declareMDoVars (← getLetDeclVars decl) mutTk?.isSome
  let body ← mkMDoOfElems xs
  mkMDoTerm decl fun decl => `(let $decl:letDecl; $body)

@[μdo_elab doLetElse]
def elabDoLetElse := adaptMDoMacroElab fun x xs => do
  let `(Term.doLetElse|let%$tk $[mut%$mutTk?]? $pat := $v | $e:doSeq) := x
    | throwAt x "ill-formed `do` let syntax"
  withRef tk do
  declareMDoVars (← getPatternVarsEx pat) mutTk?.isSome
  let e ← mkMDoOfSeq e
  let body ← mkMDoOfElems xs
  mkMDoTerm v fun v => `(if let $pat := $v then $body else $e)

@[inline]
def mkMDoIdBind
  [Monad m] [MonadQuotation m] (bindRef : Syntax)
  (id : Ident) (ty? : Option Term) (v : DoElem) (xs : Array DoElem)
: m Term := do
  let body ← mkMDoOfElems xs
  mkMDoBind bindRef (← mkMDoOfElem v) `(fun $id $[: $ty?]? => $body)

@[inline]
def mkMDoPatBind
  [Monad m] [MonadQuotation m] (bindRef : Syntax)
  (pat : Term) (v : DoElem) (e? : Option DoSeq) (xs : Array DoElem)
: m Term := do
  let patAlt ← `(Term.matchAltExpr| | $pat => $(← mkMDoOfElems xs))
  let alts ← id do
    if let some e := e? then
      let eAlt ← withRef e `(Term.matchAltExpr| | _ => μdo% $(expandDoSeq e)*)
      return #[patAlt, eAlt]
    else
      return #[patAlt]
  mkMDoBind bindRef (← mkMDoOfElem v) `(fun $alts:matchAlt*)

@[μdo_elab doLetArrow]
def elabDoLetArrow := adaptMDoMacroElab fun x xs => do
  let `(Term.doLetArrow|let%$letTk $[mut%$mutTk?]? $decl) := x
    | throwAt x "ill-formed `do` let syntax"
  withRef letTk do
  match decl with
  | `(Term.doIdDecl|$id $[: $ty?]? ←%$bindTk $v) =>
    declareMDoVar id mutTk?.isSome
    mkMDoIdBind bindTk id ty? v xs
  | `(Term.doPatDecl|$pat ←%$bindTk $v $[| $e?]?) => do
    declareMDoVars (← getPatternVarsEx pat) mutTk?.isSome
    mkMDoPatBind bindTk pat v e? xs
  | x => throwAt x "ill-formed let declaration"

@[μdo_elab doReassign]
def elabDoReassign := adaptMDoMacroElab fun x xs => withRef x do
  match x with
  | `(Term.doReassign|$id := $v) =>
    checkMDoVarReassignable id.getId
    let body ← mkMDoOfElems xs
    mkMDoTerm v fun v => `(let $id := $v; $body)
  | `(Term.doReassign|$decl:letPatDecl) =>
    checkMDoVarsReassignable (← getLetPatDeclVars decl)
    let body ← mkMDoOfElems xs
    mkMDoTerm decl fun decl => `(let $decl:letPatDecl; $body)
  | x => throwAt x "ill-formed `do` reassignment syntax"

@[μdo_elab doReassignArrow]
def elabDoReassignArrow := adaptMDoMacroElab fun x xs => withRef x do
  match x with
  | `(Term.doReassignArrow|$id:ident $[: $ty?]? ←%$bindTk $v) =>
    checkMDoVarReassignable id.getId
    mkMDoIdBind bindTk id ty? v xs
  | `(Term.doReassignArrow|$pat:term ←%$bindTk $v $[| $e?]?) =>
    checkMDoVarsReassignable (← getPatternVarsEx pat)
    mkMDoPatBind bindTk pat v e? xs
  | x => throwAt x "ill-formed `do` reassignment syntax"

@[μdo_elab doMatch]
def elabDoMatch := adaptMDoMacro fun x xs => do
  let `(Term.doMatch|match%$tk $(generalizing?)? $(motive?)? $discrs,* with $alts:matchAlt*) := x
    | throwAt x "ill-formed `do` match syntax"
  withRef tk do
  if let some motive := motive? then
    let (_, lifts) ← expandLiftMethod motive
    unless lifts.isEmpty do
      throwAt motive "cannot lift `(<- ...)` over motive"
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
  | c => throwAt c "ill-formed `do` if condition"

@[μdo_elab doIf]
def elabDoIf := adaptMDoMacro fun x xs => do
  let `(Term.doIf|if%$tk $c:doIfCond then $t $[else if $ecs:doIfCond then $ets]* $[else $e?]?) := x
    | throwAt x "ill-formed `do` if syntax"
  withRef tk do
  mkMDoJmp xs fun jmp => do
  let e ← if let some e := e? then mkMDoBranch e jmp else mkMDoEmptyBranch jmp
  let e ← (ecs.zip ets).foldrM (init := e) fun (c, t) e => do
    mkMDoIf c (← mkMDoBranch t jmp) e
  mkMDoIf c (← mkMDoBranch t jmp) e

@[μdo_elab doUnless]
def elabDoUnless := adaptMDoMacro fun x xs => do
  let `(Term.doUnless|unless%$tk $c do $x:doSeq) := x
    | throwAt x "ill-formed `do` unless syntax"
  withRef tk do
  mkMDoJmp xs fun jmp => do
  let e ← mkMDoBranch x jmp
  let t ← mkMDoEmptyBranch jmp
  mkMDoTerm c fun c => `(if $c then $t else $e)

@[μdo_elab doReturn]
def elabDoReturn := adaptMDoMacro fun x xs => do
  let `(Term.doReturn|return%$tk $(v?)?) := x
    | throwAt x "ill-formed `do` return syntax"
  withRef tk do
  checkTerminal "return" xs
  if let some v := v? then
    mkMDoTerm v fun v => ``(ret $v)
  else
    ``(halt)

@[μdo_elab doRaise]
def elabDoRaise := adaptMDoMacro fun x xs => do
  let `(doRaise|raise%$tk $(v?)?) := x
    | throwAt x "ill-formed `do` raise syntax"
  withRef tk do
  checkTerminal "raise" xs
  if let some v := v? then
    mkMDoTerm v fun v => ``(Throw.throw $v)
  else
    ``(Throw.throw ())

@[μdo_elab doFor]
def elabDoFor := adaptMDoMacroElab fun x xs => do
  let `(Term.doFor|for%$tk $ds,* do $x) := x
    | throwAt x "ill-formed `do` for syntax"
  withRef tk do
  let ds := ds.getElems
  if h : ds.size = 1 then
    let `(Term.doForDecl|$[$h? :]? $v in $it) := ds[0]
      | throwAt ds[0] "ill-formed for `in` syntax"
    let loop : Ident ← `(_μdo_loop)
    let done ← abstractMDoVars (← mkMDoOfElems xs)
    let done ← `(fun _ => $done)
    let goto ← (← getMDoScopes).applyVars (← `($loop ()))
    let body ← mkMDoBranchOfElems (expandDoSeq x |>.push goto)
    let body ← abstractMDoVars body
    let step ← `(fun $v $loop => $body)
    let iter ← ``(Iterable.iter $it $step $done)
    let iter ← (← getMDoScopes).applyVars iter
    return iter
  else
    raise "`μdo` only supports a `for` with a single `in`"
