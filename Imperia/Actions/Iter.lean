/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
namespace Imperia

/-! ## Classes -/

class Yield (α : outParam $ Type u) (μ : Type v) where
  yield' (a : α) : μ

syntax yieldStmt := withPosition("yield" (ppSpace colGt term)?)

/-! ## Syntax -/

scoped syntax:lead (name := termYield) yieldStmt : term

macro_rules
| `(yield $(x?)?) => do
  if let some x := x? then
    ``(Yield.yield' $x)
  else
    ``(Yield.yield' ())

syntax doYield := yieldStmt
attribute [scoped doElem_parser high] doYield

macro_rules | `(doElem|yield $(e?)?) => do
  let t ← `(yield $(e?)?)
  `(doElem|$t:term)
