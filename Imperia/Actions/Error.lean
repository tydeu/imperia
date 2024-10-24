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

instance [MonadLift m n] [MonadThrow ε m] : MonadThrow ε n where
  throw e := liftM (m := m) (MonadThrow.throw e)

instance (priority := low) [MonadThrow α m] [Coe β α] : MonadThrow β m where
  throw b := MonadThrow.throw (ε := α) b

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

/-- Like `throw`, but with `ε` explicit. -/
abbrev throwThe (ε : Type u) [Throw ε μ] (e : ε) : μ :=
  Throw.throw e

instance (priority := low) [Throw α μ] [Coe β α] : Throw β μ where
  throw b := Throw.throw (ε := α) b

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

/-! ## Lean Errors -/

section
open Lean

/-- Throw an error with the given location information. -/
@[inline] def throwAt [Monad m] [MonadRef m] [MonadThrow ε m] (ref : Syntax) (e : ε) : m α :=
  withRef ref (MonadThrow.throw e)

instance : MonadThrow String MacroM := ⟨Macro.throwError⟩

/-- A Lean `unsuportedSyntax` exception. -/
structure UnsupportedSyntax

@[inherit_doc UnsupportedSyntax] abbrev unsupportedSyntax := @UnsupportedSyntax.mk

instance : Coe UnsupportedSyntax Macro.Exception := ⟨fun _ => .unsupportedSyntax⟩
end

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
