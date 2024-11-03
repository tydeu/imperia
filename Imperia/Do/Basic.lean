/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Imperia.Cont
import Imperia.Util.Elab
import Imperia.Util.Syntax
import Imperia.Do.LiftMethod
import Lean.Elab.Command
import Lean.Elab.Do

open Lean Elab Term.Do Parser

namespace Imperia

/-! ## `μdo` Syntax -/

scoped syntax:arg (name := termMDo) "μdo " doSeq : term

syntax μdoNested := "μdo " doSeq
attribute [scoped doElem_parser high] μdoNested

scoped syntax:arg (name := μdoSeq) "μdo% " (ppLine doElem)+ : term

/-! ## `μdo` Syntax Utilities -/

@[inline]
def mkMDoSeq [Monad m] [MonadQuotation m] (x : DoElem) (xs : Array DoElem) : m Term := do
  withRef x `(μdo% $x $xs*)

@[inline]
def mkMDoOfSeq [Monad m] [MonadQuotation m] (x : DoSeq) : m Term := do
  withRef x ``(μdo% $(expandDoSeq x)*)

@[inline]
def mkMDoOfElem [Monad m] [MonadQuotation m] (x : DoElem) : m Term := do
  withRef x `(μdo% $x)

@[inline]
def mkMDoOfElems [Monad m] [MonadQuotation m] (xs : Array DoElem) : m Term := do
  if h : xs.size > 0 then withRef xs[0] `(μdo% $xs*) else ``(nop)

@[inline]
def mkMDoBind
  [Monad m] [MonadQuotation m]
  (ref : Syntax) (val : Term) (body : m Term)
: m Term :=
  withRef ref do `($val >>= $(← body))

@[inline]
def mkMDoBindOfLifts
  [Monad m] [MonadQuotation m]
  (lifts : Array DoLift) (body : Term)
: m Term :=
  lifts.foldrM (init := body) fun {ref, id, val} body =>
    mkMDoBind ref val `(fun $id => $body)

@[inline]
def mkMDoTerm
  [Monad m] [MonadQuotation m] [MonadThrow String m]
  (stx : TSyntax ks) (mkBody : TSyntax ks → m Term)
: m Term := do
  let (stx, lifts) ← expandLiftMethod stx
  let body ← mkBody ⟨stx⟩
  mkMDoBindOfLifts lifts body

@[inline]
def mkMDoTerms
  [Monad m] [MonadQuotation m] [MonadThrow String m]
  (xs : Array (TSyntax ks)) (mkBody : Array (TSyntax ks) → m Term)
: m Term := do
  let (xs, lifts) ← StateT.run (s := #[]) <| xs.mapM fun stx =>
    (⟨.⟩) <$> expandLiftMethodM stx
  let body ← mkBody xs
  mkMDoBindOfLifts lifts body

@[specialize]
def mkMDoAndThen
  [Monad m] [MonadQuotation m]
  (x : Term) (xs : Array DoElem)
: m Term := do
  if h : xs.size > 0 then
    mkMDoBind xs[0] x `(fun () => μdo% $xs*)
  else
    return x

/-! ## `μdo` Jumps -/

abbrev MDoJmp := Option Ident

/-- Elaboration gadget for defining jumps. -/
scoped syntax (name := μdoJump) "μdo_jump% " doElem* : term

/-- Elaboration gadget for creating a new `μdo` scope. -/
scoped syntax:arg (name := μdoBranch) "μdo_branch% " (ppLine doElem)+ : term

/-- Elaboration gadget for performing jumps. -/
syntax (name := μdoGoto) "μdo_goto% " ident : doElem

@[inline]
def mkMDoEmptyBranch [Monad m] [MonadQuotation m] (jmp : MDoJmp) : m Term :=
  if let some jmp := jmp then `(μdo_branch% μdo_goto% $jmp) else ``(nop)

@[always_inline, inline]
def mkMDoJmp
  [Monad m] [MonadQuotation m]
  (xs : Array DoElem) (f : MDoJmp → m Term)
: m Term := do
  if h : xs.size > 0 then
    let jmp : Ident ← withRef xs[0] `(_μdo_jmp)
    let body ← f jmp
    withRef xs[0]  `(let $jmp := μdo_jump% $xs*; $body)
  else
    f none

@[inline]
def mkMDoBranch [Monad m] [MonadQuotation m] (x : DoSeq) (jmp : MDoJmp) : m Term := do
  let xs := expandDoSeq x
  if let some jmp := jmp then
    let goto ← withRef jmp `(doElem|μdo_goto% $jmp)
    if h : xs.size > 0 then
      withRef xs[0] `(μdo_branch% $(xs.push goto)*)
    else
      withRef jmp `(μdo% $goto)
  else
    if h : xs.size > 0 then withRef xs[0] `(μdo_branch% $xs*) else ``(nop)

@[inline]
def mkMDo [Monad m] [MonadQuotation m] (x : DoSeq) (jmp : MDoJmp) : m Term := do
  let xs := expandDoSeq x
  if let some jmp := jmp then
    let goto ← withRef jmp `(doElem|μdo_goto% $jmp)
    if h : xs.size > 0 then
      withRef xs[0] `(μdo_branch% $(xs.push goto)*)
    else
      withRef jmp `(μdo% $goto)
  else
    if h : xs.size > 0 then withRef xs[0] `(μdo_branch% $xs*) else ``(nop)

@[specialize]
def mkMDoMatchAlts
  [Monad m] [MonadQuotation m] [MonadThrow String m]
  (alts : Array MatchAlt) (jmp : MDoJmp)
: m (Array MatchAlt) := do
  alts.mapM fun alt => withRef alt do
  let `(doMatchAlt| | $[$pats,*]|* => $x) := alt
    | raise "ill-formed `do` match alternative"
  `(Term.matchAltExpr| | $[$pats,*]|* => $(← mkMDoBranch x jmp))

@[inline]
def checkTerminal
  [Monad m] [MonadRef m] [MonadThrow String m]
  (kind : String) (xs : Array DoElem)
: m PUnit := do
  if h : xs.size > 0 then
    unless xs[0].raw.isOfKind ``μdoGoto do
      raise s!"{kind} must be the last element in a `do` sequence"

/-! ## `μdo` Extension -/

structure OptScopes (α : Type u) where
  stack : List α := []
  deriving Inhabited

abbrev OptScopes.currScope? (self : OptScopes α) : Option α :=
  self.stack.head?

abbrev OptScopes.hasScope (self : OptScopes α) : Bool :=
  !self.stack.isEmpty

def OptScopes.push (scope : α) (self : OptScopes α) : OptScopes α :=
  {self with stack := scope :: self.stack}

def OptScopes.pop (self : OptScopes α) : OptScopes α :=
  {self with stack := self.stack.tail}

@[inline] def OptScopes.modify (f : α → α) (self : OptScopes α) : OptScopes α :=
  {self with stack := match self.stack with | s :: xs => f s :: xs | [] => []}

abbrev OptScopes.any (f : α → Bool) (self : OptScopes α) : Bool :=
  self.stack.any f

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

structure MDoVar where
  name : Name
  mutable : Bool

/-- The state of a `μdo` block. -/
structure MDoScope where
  /-- Mutable variables. -/
  vars : List MDoVar := {}
  deriving Inhabited

abbrev MDoScopes := OptScopes MDoScope

initialize μdoExt : EnvExtension MDoScopes ←
  registerEnvExtension (pure {})

@[inline]
def withNewMDoScope
  [Monad m] [MonadEnv m] [MonadFinally m]
  (x : m α) (scope : MDoScope := by exact {})
: m α := do
  withNewExtScope μdoExt x scope

@[inline]
def getMDoScopes [Functor m] [MonadEnv m] : m MDoScopes :=
  μdoExt.getState <$> getEnv

@[inline]
def getMDoScope [Monad m] [MonadEnv m] [MonadError m] : m MDoScope := do
  let some scope := (← getMDoScopes).currScope?
    | raise "accessed `μdo` state outside a `μdo` block"
  return scope

@[inline]
def modifyMDoScope [MonadEnv m] (f : MDoScope → MDoScope) : m PUnit :=
  modifyEnv (μdoExt.modifyState · (·.modify f))

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
    throwAt x errMsg

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

partial def elabMDoCore
  (x : DoElem) (xs : Array DoElem) (expectedType? : Option Expr)
: TermElabM Expr := do
  withRef x do
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
      Term.withTermInfoContext' decl x (expectedType? := expectedType?) do
      Term.withMacroExpansion x xNew do
      elabMDoCore ⟨xNew⟩ xs expectedType?
    | _ =>
      elabMDoError x xs expectedType?
        m!"do element `{mkConst k}` has not been implemented for `μdo`"
  | elabFns =>
    elabMDoUsing (← saveState) x xs expectedType? elabFns

def elabMDoElems
  (xs : Array DoElem) (expectedType? : Option Expr)
: TermElabM Expr := do
  if h : 0 < xs.size then
    elabMDoCore xs[0] xs[1:] expectedType?
  else
    Term.elabTerm (← ``(nop)) expectedType?

@[term_elab μdoSeq]
def elabMDoSeq : Term.TermElab := fun stx expectedType? => do
  let `(μdo% $xs:doElem*) := stx
    | throwAt stx "ill-formed `μdo` sequence"
  elabMDoElems xs expectedType?

@[inline]
def adaptMDoMacroElab
  (f : DoElem → Array DoElem → MDoElabM Term)
: MDoElab := fun x xs expectedType? => do
  let stx ← mkMDoSeq x xs
  let exp ← f x xs
  Term.withMacroExpansion stx exp do
  Term.elabTerm exp expectedType?

@[inline]
def adaptMDoMacro (f : DoElem → Array DoElem → MacroM Term) : MDoElab :=
  adaptMDoMacroElab fun x xs => liftMacroM do f x xs

/-! ## `μdo` Implementation -/

@[term_elab termMDo] def elabMDo : Term.TermElab := fun stx expectedType? => do
  let `(μdo $x) := stx
    | throwAt stx "ill-formed `μdo` syntax"
  Term.tryPostponeIfNoneOrMVar expectedType?
  let mu ← Meta.mkFreshTypeMVar MetavarKind.synthetic
  if let some expectedType := expectedType? then
    discard <| Meta.isDefEq expectedType mu
  withNewMDoScope do
  let x ← ``(Cont.run $(← mkMDoOfSeq x))
  Term.withMacroExpansion stx x <| Term.elabTerm x mu

@[term_elab μdoBranch] def elabMDoBranch : Term.TermElab := fun stx expectedType? => do
  let `(μdo_branch% $xs*) := stx
    | throwAt stx "ill-formed `μdo_branch%` syntax"
  withNewMDoScope do
  elabMDoElems xs expectedType?

/-! ## `μdo` Mutable Variable Helpers -/

@[inline]
def MDoScopes.hasMutableVar (x : Name) (self : MDoScopes) : Bool :=
  match self.stack.findSome? (·.vars.find? (·.name == x)) with
  | some v => v.mutable
  | none => false

def declareMDoVar (var : Ident) (mutable : Bool) : MDoElabM PUnit :=
  let var := {name := var.getId, mutable}
  modifyMDoScope fun s => {s with vars := var :: s.vars}

def declareMDoVars (vars : Array Var) (mutable : Bool) : MDoElabM PUnit := do
  vars.forM fun var => declareMDoVar ⟨var⟩ mutable

def notReassignable (x : Name) : MessageData :=
  m!"`{x.simpMacroScopes}` cannot be mutated, \
  only variables declared using `let mut` can be mutated. \
  If you did not intend to mutate but define `{x.simpMacroScopes}`, \
  consider using `let {x.simpMacroScopes}` instead."

def checkMDoVarReassignable (x : Name) : MDoElabM PUnit := do
  unless (← getMDoScopes).hasMutableVar x do raise (notReassignable x)

def checkMDoVarsReassignable (vars : Array Var) : MDoElabM PUnit := do
  let scopes ← getMDoScopes
  vars.forM fun x => do
    unless scopes.hasMutableVar x.getId do
      raise (notReassignable x.getId)

def MDoScopes.abstractVars (self : MDoScopes) (x : Term) : MDoElabM Term := do
  let vs := self.stack.foldl (init := #[]) fun vs scope =>
    scope.vars.foldl (init := vs) fun vs var => vs.push (mkIdent var.name)
  withRef x `(fun $vs* => $x)

@[inline] def abstractMDoVars (x : Term) : MDoElabM Term := do
  (← getMDoScopes).abstractVars x

def MDoScopes.applyVars (self : MDoScopes) (x : Term) : MDoElabM Term := do
  withRef x do
  self.stack.foldlM (init := x) fun x scope => do
    scope.vars.foldlM (init := x) fun x var => do
      `($x $(mkIdent var.name))

@[inline] def applyMDoVars (x : Term) : MDoElabM Term := do
  MDoScopes.applyVars ((← getMDoScopes).pop) x

@[term_elab μdoJump]
def elabMDoJump : Term.TermElab := fun x expectedType? => do
  let `(μdoJump|μdo_jump% $xs*) := x
    | throwAt x "ill-formed `μdo_jump%` syntax"
  Term.elabTerm (← abstractMDoVars <| ← `(μdo% $xs*)) expectedType?
