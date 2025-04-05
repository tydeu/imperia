/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/

namespace Imperia

/-! ## Monadic Error -/

/-- Auxiliary class for inferring the error type of monads. -/
class MonadErrorOut (ε : outParam $ Type u) (m : Type v → Type w)

class MonadThrow (ε : semiOutParam $ Type u) (m : Type v → Type w) where
  throw : ε → m α

instance (priority := low) [MonadThrow ε m] : MonadErrorOut ε m where

class MonadTryCatch (ε : semiOutParam $ Type u) (m : Type v → Type w) where
  tryCatch : m α → (ε → m α) → m α

instance (priority := low) [MonadTryCatch ε m] : MonadErrorOut ε m where

instance [MonadExcept ε m] : MonadErrorOut ε m := {}
instance (priority := mid) [MonadExceptOf ε m] : MonadThrow ε m := ⟨throw⟩
instance (priority := mid) [MonadExceptOf ε m] : MonadTryCatch ε m := ⟨tryCatch⟩

instance (priority := mid) [MonadThrow ε m] [MonadTryCatch ε m] : MonadExceptOf ε m where
  throw := MonadThrow.throw
  tryCatch := MonadTryCatch.tryCatch

/-! ## Imperative Error -/

/-- Auxiliary class for inferring the error type of imperatives. -/
class ErrorOut (ε : outParam $ Type u) (μ : Type v)

instance [MonadErrorOut ε m] : ErrorOut ε (m α) := {}

class Throw (ε : semiOutParam $ Type u) (μ : Type v) where
  throw (e : ε) : μ

instance [MonadThrow ε m] : Throw ε (m α) := ⟨MonadThrow.throw⟩

instance (priority := low) [Throw ε μ] : ErrorOut ε μ := {}

class SetError (ε : semiOutParam $ Type u) (μ : Type v) where
  setError (e : ε) : μ

instance (priority := low) [SetError ε μ] : ErrorOut ε μ := {}

abbrev SetError.setTheError (ε : Type u) [SetError ε μ] (e : ε) : μ :=
  setError e

export SetError (setError setTheError)

/-! ## Unit Error -/

class MonadOrElse (m : Type u → Type v) where
  orElse : m α → (Unit → m α) → m α

instance [MonadOrElse m] : OrElse (m α) := ⟨MonadOrElse.orElse⟩
instance (priority := mid) [MonadOrElse m] : MonadTryCatch Unit m := ⟨MonadOrElse.orElse⟩

@[inline, always_inline]
def MonadTryCatch.orElse [MonadTryCatch ε m] (x : m α) (h : Unit → m α) : m α :=
  MonadTryCatch.tryCatch x fun (_ : ε) => h ()

abbrev MonadOrElse.ofTryCatchThe (ε) [MonadTryCatch ε m] : MonadOrElse m where
  orElse := MonadTryCatch.orElse (ε := ε)

abbrev MonadOrElse.ofTryCatch [MonadTryCatch ε m] : MonadOrElse m :=
  ofTryCatchThe ε

instance (priority := mid) [Alternative m] : MonadOrElse m := ⟨Alternative.orElse⟩
instance (priority := mid) [Alternative m] : MonadThrow Unit m := ⟨fun _ => Alternative.failure⟩

instance (priority := mid) [Applicative m] [MonadThrow Unit m] [MonadOrElse m] : Alternative m where
  failure := MonadThrow.throw ()
  orElse := MonadOrElse.orElse

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
