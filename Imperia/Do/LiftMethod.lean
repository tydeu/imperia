/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Parser.Do

/-! ## Lift Method

This module contains a generalized adaption of
`Lean.Elab.Term.Do.ToCodeBlock.expandLiftMethod` from the Lean core.
It extracts nested `(<- ...)` terms from syntax.
-/

open Lean

namespace Imperia

/-- Return true if we should not lift `(<- ...)` actions nested in the syntax nodes with the given kind. -/
def liftMethodDelimiter (k : SyntaxNodeKind) : Bool :=
  k == ``Parser.Term.do ||
  k == ``Parser.Term.doSeqIndent ||
  k == ``Parser.Term.doSeqBracketed ||
  k == ``Parser.Term.termReturn ||
  k == ``Parser.Term.termUnless ||
  k == ``Parser.Term.termTry ||
  k == ``Parser.Term.termFor

partial def hasLiftMethod : Syntax → Bool
  | Syntax.node _ k args =>
    if liftMethodDelimiter k then false
    -- NOTE: We don't check for lifts in quotations here, which doesn't break anything but merely makes this rare case a
    -- bit slower
    else if k == ``Parser.Term.liftMethod then true
    -- For `pure` if-then-else, we only lift `(<- ...)` occurring in the condition.
    else if k == ``termDepIfThenElse || k == ``termIfThenElse then args.size >= 2 && hasLiftMethod args[1]!
    else args.any hasLiftMethod
  | _ => false

def letDeclArgHasBinders (letDeclArg : Syntax) : Bool :=
  let k := letDeclArg.getKind
  if k == ``Parser.Term.letPatDecl then
    false
  else if k == ``Parser.Term.letEqnsDecl then
    true
  else if k == ``Parser.Term.letIdDecl then
    -- letIdLhs := binderIdent >> checkWsBefore "expected space before binders" >> many (ppSpace >> letIdBinder)) >> optType
    let binders := letDeclArg[1]
    binders.getNumArgs > 0
  else
    false

def letDeclHasBinders (letDecl : Syntax) : Bool :=
  letDeclArgHasBinders letDecl[0]

def liftMethodForbiddenBinder (stx : Syntax) : Bool :=
  let k := stx.getKind
  -- TODO: make this extensible in the future.
  if k == ``Parser.Term.fun || k == ``Parser.Term.matchAlts ||
     k == ``Parser.Term.doLetRec || k == ``Parser.Term.letrec then
     -- It is never ok to lift over this kind of binder
    true
  -- The following kinds of `let`-expressions require extra checks to decide whether they contain binders or not
  else if k == ``Parser.Term.let then
    letDeclHasBinders stx[1]
  else if k == ``Parser.Term.doLet then
    letDeclHasBinders stx[2]
  else if k == ``Parser.Term.doLetArrow then
    letDeclArgHasBinders stx[2]
  else
    false

structure DoLift where
  ref : Syntax
  id : Ident
  val : Term
  deriving BEq

variable (baseId : Name) in
partial def expandLiftMethodAux (inQuot : Bool) (inBinder : Bool) : Syntax → StateT (Array DoLift) MacroM Syntax
  | stx@(Syntax.node i k args) =>
    if k == choiceKind then do
      -- choice node: check that lifts are consistent
      let alts ← stx.getArgs.mapM (expandLiftMethodAux inQuot inBinder · |>.run #[])
      let (_, lifts) := alts[0]!
      unless alts.all (·.2 == lifts) do
        Macro.throwErrorAt stx "cannot lift `(<- ...)` over inconsistent syntax variants, consider lifting out the binding manually"
      modify (· ++ lifts)
      return .node i k (alts.map (·.1))
    else if liftMethodDelimiter k then
      return stx
    -- For `pure` if-then-else, we only lift `(<- ...)` occurring in the condition.
    else if args.size >= 2 && (k == ``termDepIfThenElse || k == ``termIfThenElse) then do
      let inAntiquot := stx.isAntiquot && !stx.isEscapedAntiquot
      let arg1 ← expandLiftMethodAux (inQuot && !inAntiquot || stx.isQuot) inBinder args[1]!
      let args := args.set! 1 arg1
      return Syntax.node i k args
    else if k == ``Parser.Term.liftMethod && !inQuot then withFreshMacroScope do
      if inBinder then
        Macro.throwErrorAt stx "cannot lift `(<- ...)` over a binder, this error usually happens when you are trying to lift a method nested in a `fun`, `let`, or `match`-alternative, and it can often be fixed by adding a missing `do`"
      let ref := args[0]!
      let term := args[1]!
      let term  ← expandLiftMethodAux inQuot inBinder term
      -- keep name deterministic across choice branches
      let id ← mkIdentFromRef (.num baseId (← get).size)
      modify fun s => s.push ⟨ref, id, ⟨term⟩⟩
      return id
    else do
      let inAntiquot := stx.isAntiquot && !stx.isEscapedAntiquot
      let inBinder   := inBinder || (!inQuot && liftMethodForbiddenBinder stx)
      let args ← args.mapM (expandLiftMethodAux (inQuot && !inAntiquot || stx.isQuot) inBinder)
      return Syntax.node i k args
  | stx => return stx

def expandLiftMethodM (stx : Syntax) : StateT (Array DoLift) MacroM Syntax := do
  if !hasLiftMethod stx then
    return stx
  else
    let baseId ← withFreshMacroScope (MonadQuotation.addMacroScope `_μdo_lift)
    expandLiftMethodAux baseId false false stx

def expandLiftMethod (stx : Syntax) : MacroM (Syntax × Array DoLift) := do
  expandLiftMethodM stx |>.run #[]
