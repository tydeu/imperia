/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/

open Lean

namespace Imperia

/--
Monads which support `Macro.Exception` errors.
Used to define functions which can error and are polymorphic
between `MacroM` and the elaboration monads (i.e., `TermElabM`)
-/
class MonadMacroError (m : Type u → Type v) where
  throwAt' (ref : Syntax) (msg : String) : m α
  throwUnsupported : m α

instance : MonadMacroError MacroM where
  throwAt' ref msg := throw (.error ref msg)
  throwUnsupported := throw .unsupportedSyntax

namespace MonadMacroError

instance [MonadLift m n] [MonadMacroError m] : MonadMacroError n where
  throwAt' ref msg := liftM (m := m) <| MonadMacroError.throwAt' ref msg
  throwUnsupported := liftM (m := m) <| MonadMacroError.throwUnsupported

@[inherit_doc Macro.throwError]
protected def throw [Bind m] [MonadRef m] [MonadMacroError m] (msg : String) : m α :=
  getRef >>= fun ref => throwAt' ref msg

@[inherit_doc Macro.throwErrorAt]
protected def throwAt [Bind m] [MonadRef m] [MonadMacroError m] (ref : Syntax) (msg : String) : m α :=
  getRef >>= fun oldRef => throwAt' (replaceRef ref oldRef) msg
