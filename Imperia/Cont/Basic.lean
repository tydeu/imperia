/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Imperia.Actions.Basic

/-! # The Continuation Monad -/

namespace Imperia

/--
The `Cont` type defines a continuation monad
over the imperative type `μ`.
It is used by Imperia to define `μdo`, its alternative `do` notation,
using local continuation passing style (CPS).

Since CPS is not performant in the Lean runtime,
definitions using the `Cont` monad must be inlined away.
The primitives defined and used by Imperia are all marked
`@[always_inline, inline]` to ensure this happens.
Users defining their own combinators should do likewise.
If a function is too complex to inline, it should be defined
using standard monads instead of `Cont`.
-/
def Cont (μ : Type u) (α : Type v) :=
  (α → μ) → μ

namespace Cont

@[always_inline, inline] abbrev mk (f : (α → μ) → μ) : Cont μ α :=
  f

@[always_inline, inline, pp_nodot] abbrev app (x : Cont μ α) (k : α → μ) : μ :=
  x k

@[simp] theorem app_mk : mk f h = f h := rfl

/-- Run the CPS monad, producing the underlying imperative. -/
@[always_inline, inline, pp_nodot] abbrev run (x : Cont μ Empty) : μ :=
 x Empty.elim

/-! ## The `Cont` Monad -/

/-- The `pure` operation of the `Cont` monad. -/
@[always_inline, inline] protected def pure (a : α) : Cont μ α :=
  fun k => k a

instance : Pure (Cont μ) := ⟨Cont.pure⟩

@[simp] theorem app_pure : (pure a : Cont μ α) k = k a := rfl

/-- The `bind` operation of the `Cont` monad. -/
@[always_inline, inline]
protected def bind (x : Cont μ α) (f : α → Cont μ β) : Cont μ β :=
  fun k => x.app fun a => f a k

instance : Bind (Cont μ) := ⟨Cont.bind⟩

@[simp] theorem app_bind {x : Cont μ α} :
  bind x f k = x.app fun a => f a k
:= rfl

instance : Monad (Cont μ) := {}

@[simp] theorem app_map {x : Cont μ α} :
  Functor.map f x k = x.app fun a => k (f a)
:= rfl

/-! ## Lifting imperatives into `Cont` -/

/-- Lift an imperative into `Cont`. -/
@[always_inline, inline] def lift [HBind α ξ μ] (x : ξ) : Cont μ α :=
  hBind x

instance [AndThen μ] : Coe μ (Cont μ Unit) := ⟨Cont.lift⟩

@[simp] theorem app_lift [AndThen μ] {x : μ} :
  (lift x : Cont μ Unit) k = x >> k ()
:= rfl

instance [Bind m] : Coe (m α) (Cont (m α) α) := ⟨Cont.lift⟩
instance [Bind m] : MonadLift m (Cont (m α)) := ⟨Cont.lift⟩

@[simp] theorem eq_liftM [Bind m] : (Cont.lift x : Cont (m β) α) = liftM x := rfl
@[simp] theorem liftM_eq_bind [Bind m] : (liftM x : Cont (m β) α) = bind x := rfl

instance : MonadFunctor m (Cont (m β)) where
  monadMap f x := fun k => f (x k)

/-! ## Termination -/

/--
Transfer control flow from the `Cont` monad
to the imperative `x` (and never resume).
-/
@[always_inline, inline] def exec (x : μ) : Cont μ α :=
  fun _ => x

instance : Coe μ (Cont μ Empty) := ⟨exec⟩

@[simp] theorem app_exec : exec x k = x := rfl
@[simp] theorem bind_exec : bind (exec x) f = exec x := rfl

instance : Coe μ (Cont (Cont μ α) Empty) := ⟨fun x => (exec (exec x))⟩

/-- **Void return.** Terminate control flow by transferring control to a no-op. -/
@[always_inline, inline] protected def halt [Nop μ] : Cont μ α :=
  exec nop

instance [Nop μ] : Halt (Cont μ α) := ⟨Cont.halt⟩

@[simp] theorem app_halt [Nop μ] : (halt : Cont μ α) k = nop := rfl

instance [Nop μ] : Nop (Cont μ Empty) := ⟨halt⟩

@[simp] theorem nop_eq_halt [Nop μ] : (nop : Cont μ Empty) = halt := rfl

/-- **Early return.** Set `a` as the return value and halt. -/
@[always_inline, inline] protected def ret [SetReturn α μ] (a : α) : Cont μ β :=
  exec (setReturn a)

instance [SetReturn α μ] : Ret α (Cont μ β) := ⟨Cont.ret⟩

@[simp] theorem app_ret [SetReturn α μ] : (ret a : Cont μ β) k = setReturn a := rfl

/-- Run the CPS monad, discarding the result and returning the underlying imperative. -/
@[always_inline, inline, pp_nodot] abbrev run' [Nop μ] (x : Cont μ α) : μ :=
  x fun _ => nop

instance [Nop μ] : Coe (Cont μ Unit) (Cont μ Empty) := ⟨(·.run')⟩

/-- Run the CPS monad, returning the result through the underlying monad. -/
@[always_inline, inline, pp_nodot] abbrev runM [Pure m] (x : Cont (m α) α) : m α :=
  x pure

/--
Run `x` as independent imperative block.
Control flow manipulation within `x` is restricted to the block.
For instance, returns within `x` will be caught here and not halt the outer `Cont`.
-/
@[always_inline, inline, pp_nodot]
def block [Coe μ (Cont μ α)] (x : Cont μ Empty) : Cont μ α :=
  ↑(run x)

@[simp] theorem block_eq_lift [AndThen μ] :
  (block x : Cont μ Unit) = lift (run x)
:= rfl

@[simp] theorem block_eq_exec :
  (block x : Cont μ Empty)  = exec (run x)
:= rfl

/-! ## Lemma Extras -/

@[simp] theorem app_ite [Decidable c] {t e : Cont μ α} :
  ite c t e k = ite c (t k) (e k)
:= by split <;> rfl

@[simp] theorem app_dite [Decidable c] {t : c → Cont μ α} {e : ¬ c → Cont μ α} :
  dite c t e k = dite c (fun h => t h k) (fun h => e h k)
:= by split <;> rfl
