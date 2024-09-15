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

syntax μdoNested := "μdo " doSeq
attribute [scoped doElem_parser high] μdoNested

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

abbrev MDoJmp := Option Ident

@[inline] def MDoJmp.mkTerm (jmp : MDoJmp) : MacroM Term :=
  if let some jmp := jmp then pure jmp else ``(nop)

@[always_inline, inline]
def mkMDoJmp (xs : Array DoElem) (f : MDoJmp → MacroM Term) : MacroM Term := do
  if h : xs.size > 0 then
    let jmp : Ident ← withRef xs[0] `(_μdo_jmp)
    let body ← f jmp
    withRef xs[0]  `(let $jmp := μdo% $xs*; $body)
  else
    f none

@[inline]
def mkMDoSeqJmp (x : DoSeq) (jmp : MDoJmp) : MacroM Term := do
  let x ← mkMDoOfSeq x
  if let some jmp := jmp then
    mkMDoBind jmp x `(fun () => $jmp)
  else
    return x

def mkMDoMatchAlts (alts : Array MatchAlt) (jmp : MDoJmp) : MacroM (Array MatchAlt) := do
  alts.mapM fun alt => do
  let `(doMatchAlt| | $[$pats,*]|* => $x) := alt
    | Macro.throwErrorAt alt "ill-formed `do` match alternative"
  `(Term.matchAltExpr| | $[$pats,*]|* => $(← mkMDoSeqJmp x jmp))

/-! ## `μdo` Extension -/

structure OptScopes (α : Type u) where
  currScope? : Option α := none
  parentScopes : List α := []
  deriving Inhabited

abbrev OptScopes.hasScope (self : OptScopes α) : Bool :=
  self.currScope?.isSome

def OptScopes.push (scope : α) (self : OptScopes α) : OptScopes α :=
  match self with
  | ⟨none, ps⟩ => ⟨some scope, ps⟩
  | ⟨some prev, ps⟩ => ⟨some scope, prev :: ps⟩

def OptScopes.pop (self : OptScopes α) : OptScopes α :=
  match self with
  | ⟨_, []⟩ => ⟨none, []⟩
  | ⟨_, prev::ps⟩ => ⟨some prev, ps⟩

@[inline]
def withNewExtScope
  [Monad m] [MonadEnv m] [MonadFinally m]
  (ext : EnvExtension (OptScopes α)) (x : m β) (scope : α := by exact {})
: m β := do
  modifyEnv (ext.modifyState · (·.push scope))
  try
    x
  finally
    modifyEnv (ext.modifyState · (·.pop))

/-- The state of a `μdo` block. -/
structure MDoState where
  deriving Inhabited

abbrev MDoScopes := OptScopes MDoState

initialize μdoExt : EnvExtension MDoScopes ←
  registerEnvExtension (pure {})

/-! ## `μdo` Elab Attribute -/

abbrev MDoElabM := TermElabM
abbrev MDoElab := DoElem → Array DoElem → Option Expr → MDoElabM Expr

initialize μdoElabAttr : KeyedDeclsAttribute MDoElab ←
  unsafe mkElabAttribute MDoElab `builtin_μdo_elab `μdo_elab `Lean.Parser.Term ``MDoElab "μdo"

def elabMDoError
  (x : DoElem) (xs : Array DoElem)
  (expectedType? : Option Expr) (errMsg : MessageData)
: TermElabM Expr := do
  if h : xs.size > 0 then
    logErrorAt x errMsg
    let x ← withRef xs[0] `(μdo% $xs*)
    Term.elabTerm x expectedType?
  else
    throwErrorAt x errMsg

def elabMDoUsing
  (s : Term.SavedState)
  (x : DoElem) (xs : Array DoElem) (expectedType? : Option Expr)
  (elabFns : List (KeyedDeclsAttribute.AttributeEntry MDoElab) )
: TermElabM Expr := do
  if let elabFn::elabFns := elabFns then
    try
      Term.withTermInfoContext' elabFn.declName x (expectedType? := expectedType?) do
        elabFn.value x xs expectedType?
    catch
      | ex@(.internal id _) =>
        if id == unsupportedSyntaxExceptionId then
          s.restore
          elabMDoUsing s x xs expectedType? elabFns
        else
          throw ex
      | ex =>
        throw ex
  else
    elabMDoError x xs expectedType?
      m!"`μdo` elaborator(s) were unable to process the do element syntax{indentD x}"

@[term_elab μdoSeq]
def elabMDoSeq : Term.TermElab := fun stx expectedType? => do
  let `(μdo% $x $xs:doElem*) := stx
    | throwErrorAt stx "ill-formed `μdo` sequence"
  let k := x.raw.getKind
  withTraceNode `Elab.step
    (fun _ => return m!"expected type: {expectedType?}, μdo element '{k}'\n{x}")
    (tag := k.toString) do
  let env ← getEnv
  match μdoElabAttr.getEntries env k with
  | [] =>
    withFreshMacroScope do withIncRecDepth do
    match (← liftMacroM (expandMacroImpl? env x)) with
    | some (decl, xNew?) =>
      let xNew ← liftMacroM <| liftExcept xNew?
      let stxNew ← withRef stx `(μdo% $(⟨xNew⟩) $xs*)
      Term.withTermInfoContext' decl x (expectedType? := expectedType?) do
      Term.withMacroExpansion stx stxNew do
      withRef stxNew <| Term.elabTerm stxNew expectedType?
    | _ =>
      elabMDoError x xs expectedType?
        m!"do element `{mkConst k}` has not been implemented for `μdo`"
  | elabFns =>
    elabMDoUsing (← saveState) x xs expectedType? elabFns

@[inline]
def adaptMDoMacroElab
  (f : DoElem → Array DoElem → MDoElabM Term)
: MDoElab := fun x xs expectedType? => do
  let stx ← `(μdo% $x $xs*)
  let exp ← do f x xs
  Term.withMacroExpansion stx exp do
  Term.elabTerm exp expectedType?

@[inline]
def adaptMDoMacro (f : DoElem → Array DoElem → MacroM Term) : MDoElab :=
  adaptMDoMacroElab fun x xs => liftMacroM do f x xs

/-! ## `μdo` Implementation -/

@[term_elab termMDo] def elabMDo : Term.TermElab := fun stx expectedType? => do
  let `(μdo $x) := stx
    | throwErrorAt stx "ill-formed `μdo` syntax"
  Term.tryPostponeIfNoneOrMVar expectedType?
  let mu ← Meta.mkFreshTypeMVar MetavarKind.synthetic
  if let some expectedType := expectedType? then
    discard <| Meta.isDefEq expectedType mu
  withNewExtScope μdoExt do
  let x ← liftMacroM do ``(Cont.run $(← mkMDoOfSeq x))
  Term.withMacroExpansion stx x <| Term.elabTerm x mu
