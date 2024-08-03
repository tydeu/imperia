/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Imperia.Cont
import Imperia.Util.Syntax
import Imperia.Do.LiftMethod
import Lean.Elab.Command

open Lean Parser Elab

namespace Imperia

/-! ## `μdo` Syntax -/

scoped syntax:arg (name := termMDo) "μdo " doSeq : term
scoped syntax:arg (name := μdoNested) (priority := high) "μdo " doSeq : doElem
scoped syntax:arg (name := μdoSeq) "μdo% " (ppLine doElem)+ : term

/-! ## `μdo` Syntax Utilities -/

def mkMDoOfSeq (x : DoSeq) : MacroM Term := do
  withRef x ``(μdo% $(← expandDoSeq x)*)

def mkMDoOfElem (x : DoElem) : MacroM Term := do
  withRef x `(μdo% $x)

def mkMDoOfElems (xs : Array DoElem) : MacroM Term := do
  if h : xs.size > 0 then withRef xs[0] `(μdo% $xs*) else ``(nop)

@[inline]
def mkMDoBind (ref : Syntax) (val : Term) (body : MacroM Term) : MacroM Term :=
  withRef ref do `($val >>= $(← body))

def mkMDoBindOfLifts (lifts : Array DoLift) (body : Term) : MacroM Term :=
  lifts.foldrM (init := body) fun {ref, id, val} body =>
    mkMDoBind ref val `(fun $id => $body)

@[inline] def mkMDoTerm (stx : TSyntax ks) (mkBody : TSyntax ks → MacroM Term) : MacroM Term := do
  let (stx, lifts) ← expandLiftMethod stx
  let body ← mkBody ⟨stx⟩
  mkMDoBindOfLifts lifts body

@[inline] def mkMDoTerms (xs : Array (TSyntax ks)) (mkBody : Array (TSyntax ks) → MacroM Term) : MacroM Term := do
  let (xs, lifts) ← StateT.run (s := #[]) <| xs.mapM fun stx =>
    (⟨.⟩) <$> expandLiftMethodM stx
  let body ← mkBody xs
  mkMDoBindOfLifts lifts body

def mkMDoAndThen (x : Term) (xs : Array DoElem) : MacroM Term := do
  if h : xs.size > 0 then
    mkMDoBind xs[0] x `(fun () => μdo% $xs*)
  else
    return x

abbrev doMatchAlt := Term.matchAlt Term.doSeq

def mkMDoMatchAlt (alt : TSyntax ``Term.matchAlt) : MacroM (TSyntax ``Term.matchAlt) := do
  let `(doMatchAlt| | $[$pats,*]|* => $x) := alt
    | Macro.throwErrorAt alt "ill-formed `do` match alternative"
  `(Term.matchAltExpr| | $[$pats,*]|* => $(← mkMDoOfSeq x))

@[always_inline, inline]
def mkMDoJmp
  [Monad m] [MonadQuotation m]
  (xs : Array DoElem) (h : xs.size > 0) (f : Ident → m Term)
: m Term := do
  let jmp : Ident ← withRef xs[0] `(_μdo_jmp)
  let body ← f jmp
  withRef xs[0]  `(let $jmp := μdo% $xs*; $body)

@[inline]
def mkMDoSeqThenJmp (x : DoSeq) (jmp : Ident) : MacroM Term := do
  mkMDoAndThen (← mkMDoOfSeq x) #[jmp]

/-! ## `μdo` Implementations -/

macro_rules
| `(μdo $x) => do ``(Cont.run $(← mkMDoOfSeq x))

elab_rules : term
| `(μdo% $x $xs:doElem*) => do
  let kind := mkConst x.raw.getKind
  logErrorAt x m!"do element `{kind}` has not been implemented for `μdo`"
  Term.elabTerm (← `(μdo% $xs*)) none
