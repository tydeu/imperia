/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/

namespace Imperia

/-! ## Monadic Error -/

/-- Auxiliary class for inferring the errpr type of imperatives. -/
class ErrorOut (ε : outParam $ Type u) (μ : Type v)

instance [MonadExcept ε m] : ErrorOut ε (m PUnit) where

class MonadThrow (ε : semiOutParam $ Type u) (m : Type v → Type w) where
  throw : ε → m α

instance [MonadExceptOf ε m] : MonadThrow ε m := ⟨throw⟩

instance (priority := low) [MonadThrow ε m] : ErrorOut ε (m PUnit) where

class MonadTryCatch (ε : semiOutParam $ Type u) (m : Type v → Type w) where
  tryCatch : m α → (ε → m α) → m α

instance [MonadExceptOf ε m] : MonadTryCatch ε m := ⟨tryCatch⟩

instance (priority := low) [MonadTryCatch ε m] : ErrorOut ε (m PUnit) where

instance [MonadThrow ε m] [MonadTryCatch ε m] : MonadExceptOf ε m where
  throw := MonadThrow.throw
  tryCatch := MonadTryCatch.tryCatch

/-! ## Imperative Error -/

class Throw (ε : semiOutParam $ Type u) (μ : Type v) where
  throw (e : ε) : μ

instance [MonadThrow ε m] : Throw ε (m α) := ⟨MonadThrow.throw⟩

instance (priority := low) [Throw ε μ] : ErrorOut ε μ where

class SetError (ε : semiOutParam $ Type u) (μ : Type v) where
  setError (e : ε) : μ

instance (priority := low) [SetError ε μ] : ErrorOut ε μ where

abbrev setError [SetError ε μ] (e : ε) : μ :=
  SetError.setError e

abbrev setTheError (ε : Type u) [SetError ε μ] (e : ε) : μ :=
  setError e

/-! ## Unit Error -/

instance [MonadTryCatch PUnit m] : OrElse (m α) := ⟨MonadTryCatch.tryCatch⟩

instance (priority := low) [Alternative m] : MonadExceptOf PUnit m where
  throw _ := Alternative.failure
  tryCatch := Alternative.orElse

instance (priority := low) [Applicative m] [MonadExceptOf PUnit m] : Alternative m where
  failure := throw ()
  orElse := tryCatch

/-! ## Syntax Sugar -/

syntax raiseStmt := withPosition("raise" (ppSpace colGt term)?)

scoped syntax:lead (name := termRaise) raiseStmt : term

macro_rules
| `(raise $(x?)?) => do
  if let some x := x? then
    ``(Throw.throw $x)
  else
    ``(Throw.throw ())

syntax doRaise := raiseStmt
attribute [scoped doElem_parser high] doRaise

macro_rules | `(doElem|raise $(e?)?) => do
  let t ← `(raise $(e?)?)
  `(doElem|$t:term)
