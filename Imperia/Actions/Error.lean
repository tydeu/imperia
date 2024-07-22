/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/

namespace Imperia

/-! ## Monadic Error -/

/-- Auxiliary class for inferring the errpr type of imperatives. -/
class ErrorOut (ε : outParam $ Type u) (μ : Type v)

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

instance [MonadExcept ε m] : ErrorOut ε (m PUnit) where

/-! ## Imperative Error -/

class Throw (ε : semiOutParam $ Type u) (μ : Type v) where
  throw (e : ε) : μ

instance [MonadThrow ε m] : Throw ε (m α) := ⟨MonadThrow.throw⟩

class SetError (ε : semiOutParam $ Type u) (μ : Type v) where
  setError (e : ε) : μ

instance (priority := low) [SetError ε μ] : ErrorOut ε μ where

abbrev setError [SetError ε μ] (e : ε) : μ :=
  SetError.setError e

abbrev setTheError (ε : Type u) [SetError ε μ] (e : ε) : μ :=
  setError e

class TryCatch (ε : semiOutParam $ Type u) (μ : Type v) where
  tryCatch : μ → (ε → μ) → μ

instance [MonadTryCatch ε m] : TryCatch ε (m α) := ⟨MonadTryCatch.tryCatch⟩

class HTryCatch (ε : semiOutParam $ Type u) (μ : Type v) (ξ : Type v) where
  tryCatch : μ → (ε → ξ) → ξ

@[default_instance] instance [TryCatch ε μ] : HTryCatch ε μ μ := ⟨TryCatch.tryCatch⟩

abbrev HTryCatch.tryCatchThe (ε : Type u) [HTryCatch ε μ ξ] (x : μ) (f : ε → ξ) : ξ :=
  HTryCatch.tryCatch (ε := ε) x f

abbrev HTryCatch.tryCatchOut [ErrorOut μ ε] [HTryCatch ε μ ξ] (x : μ) (f : ε → ξ) : ξ :=
  HTryCatch.tryCatch (ε := ε) x f

class TryFinally (μ : Type v) where
  tryFinally : μ → μ → μ

instance [MonadFinally m] [Functor m] : TryFinally (m α) := ⟨tryFinally⟩

/-! ## Unit Error -/

class Failure (μ : Type v) where
  failure : μ

instance (priority := low) [Failure μ] : Throw Unit μ := ⟨fun _ => Failure.failure⟩

class MonadFailure (m : Type u → Type v) where
  failure : m α

instance [MonadFailure m] : Failure (m α) := ⟨MonadFailure.failure⟩
instance [Alternative m] : MonadFailure m := ⟨failure⟩

export Failure (failure)

class MonadOrElse (m : Type u → Type v) where
  orElse : m α → (Unit → m α) → m α

instance [MonadOrElse m] : OrElse (m α) := ⟨MonadOrElse.orElse⟩
instance [Alternative m] : MonadOrElse m := ⟨Alternative.orElse⟩

instance
  [Pure m] [Seq m] [SeqLeft m] [SeqRight m] [MonadFailure m] [MonadOrElse m]
: Alternative m where
  failure := MonadFailure.failure
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

syntax (name := doRaise) (priority := high) raiseStmt : doElem
macro_rules | `(doElem|raise $(e?)?) => `(raise $(e?)?)
