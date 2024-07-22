/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Meta.Tactic.Simp.Simproc

namespace String
open Lean Meta Simp

instance : ToExpr String.Pos where
  toExpr p := mkApp (mkConst ``String.Pos.mk) (toExpr p.byteIdx)
  toTypeExpr := mkConst ``String.Pos

/-- Return `some p` if `e` is a `String.Pos` formed from a natural literal. -/
def getStringPosValue? (e : Expr) : MetaM (Option String.Pos) := do
  match_expr e with
  | String.Pos.mk e => (·.map (⟨·⟩)) <$> getNatValue? e
  | _ => (·.map (⟨·.1⟩)) <$> getOfNatValue? e ``String.Pos

simproc [simp] reduceGet (String.get _ _) := fun e => do
  let_expr String.get s p ← e | return .continue
  let .lit (.strVal s) := s | return .continue
  let some p ← getStringPosValue? p | return .continue
  return .done { expr := toExpr (s.get p) }

simproc [simp] reduceNext (String.next _ _) := fun e => do
  let_expr String.next s p ← e | return .continue
  let .lit (.strVal s) := s | return .continue
  let some p ← getStringPosValue? p | return .continue
  return .done { expr := toExpr (s.next p) }

simproc [simp] reduceAtEnd (String.atEnd _ _) := fun e => do
  let_expr String.atEnd s p ← e | return .continue
  let .lit (.strVal s) := s | return .continue
  let some p ← getStringPosValue? p | return .continue
  return .done { expr := toExpr (s.atEnd p) }

simproc [simp] reduceUtf8ByteSize (String.utf8ByteSize _) := fun e => do
  let_expr String.utf8ByteSize s ← e | return .continue
  let .lit (.strVal s) := s | return .continue
  return .done { expr := toExpr (s.utf8ByteSize) }

simproc [simp] reduceCSize (String.csize _) := fun e => do
  let_expr String.csize c ← e | return .continue
  let_expr Char.ofNat c ← c | return .continue
  let .lit (.natVal c) := c | return .continue
  return .done { expr := toExpr (String.csize (Char.ofNat c)) }

end String
