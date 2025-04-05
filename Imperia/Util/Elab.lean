/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Exception
import Lean.Elab.Exception
import Imperia.Actions.Error

open Lean

namespace Imperia

instance : Coe UnsupportedSyntax Exception where
  coe _  := .internal Elab.unsupportedSyntaxExceptionId

instance [Monad m] [MonadError m] : MonadThrow MessageData m := ⟨Lean.throwError⟩
