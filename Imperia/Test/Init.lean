/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Meta.Tactic.Simp.Simproc

open Lean Meta Simp

instance : ToExpr String.Pos where
  toExpr p := mkApp (mkConst ``String.Pos.mk) (toExpr p.byteIdx)
  toTypeExpr := mkConst ``String.Pos

/-- Return `some p` if `e` is a `String.Pos` formed from a natural literal. -/
def getStringPosValue? (e : Expr) : MetaM (Option String.Pos) := do
  match_expr e with
  | String.Pos.mk e => (·.map (⟨·⟩)) <$> getNatValue? e
  | _ => (·.map (⟨·.1⟩)) <$> getOfNatValue? e ``String.Pos

namespace String

simproc [simp] reduceGet (String.get _ _) := fun e => do
  let_expr String.get s p ← e | return .continue
  let some s := getStringValue? s | return .continue
  let some p ← getStringPosValue? p | return .continue
  return .done { expr := toExpr (s.get p) }

simproc [simp] reduceNext (String.next _ _) := fun e => do
  let_expr String.next s p ← e | return .continue
  let some s := getStringValue? s | return .continue
  let some p ← getStringPosValue? p | return .continue
  return .done { expr := toExpr (s.next p) }

simproc [simp] reduceAtEnd (String.atEnd _ _) := fun e => do
  let_expr String.atEnd s p ← e | return .continue
  let some s := getStringValue? s | return .continue
  let some p ← getStringPosValue? p | return .continue
  return .done { expr := toExpr (s.atEnd p) }

simproc [simp] reduceUtf8ByteSize (String.utf8ByteSize _) := fun e => do
  let_expr String.utf8ByteSize s ← e | return .continue
  let some s := getStringValue? s | return .continue
  return .done { expr := toExpr s.utf8ByteSize }

end String

simproc [simp] Char.reduceUtf8Size (Char.utf8Size _) := fun e => do
  let_expr Char.utf8Size c ← e | return .continue
  let some c ← getCharValue? c | return .continue
  return .done { expr := toExpr c.utf8Size }
