/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Imperia.Actions
import Imperia.Cont.Basic

namespace Imperia.Cont

instance [SetState σ μ] : SetState σ (Cont μ Empty) where
  set s := exec (setState s)

instance [SetState σ μ] [AndThen μ] : SetState σ (Cont μ Unit) where
  set s := lift (setState s)

instance [ModifyState σ μ] : ModifyState σ (Cont μ Empty) where
  modify f := exec (modifyState f)

instance [ModifyState σ μ] [AndThen μ] : ModifyState σ (Cont μ Unit) where
  modify f := lift (modifyState f)

instance [SetError ε μ] : MonadThrow ε (Cont μ) where
  throw e := exec (setError e)

@[simp] theorem app_throw_of_setError [SetError ε μ] (e : ε) :
  (Throw.throw e : Cont μ α) k = setError e
:= rfl

instance [Throw ε μ] : MonadThrow ε (Cont μ) where
  throw e := exec (Throw.throw e)

@[simp] theorem app_throw_of_throw [Throw ε μ] (e : ε) :
  (Throw.throw e : Cont μ α) k = Throw.throw e
:= rfl

instance [SetError ε μ] : SetError ε (Cont μ Empty) where
  setError e := exec (setError e)

instance [SetError ε μ] [AndThen μ] : SetError ε (Cont μ Unit) where
  setError e := lift (setError e)

instance [Failure μ] : MonadFailure (Cont μ) where
  failure := exec failure
