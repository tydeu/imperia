/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/

namespace Imperia

/-- Auxiliary class for inferring the state type of imperatives. -/
class StateOut (σ : outParam $ Type u) (μ : Type v)

/-- Auxiliary class for inferring the state type of monads. -/
class MonadStateOut (σ : outParam $ Type u) (m : Type u → Type v)

instance [MonadStateOut σ m] : StateOut σ (m α) where

instance [MonadState σ m] : MonadStateOut σ m where

/-! ## Get State -/

class GetState (σ : semiOutParam $ Type u) (m : Type u → Type v) where
  getState : m σ

instance (priority := low) [GetState σ m] : MonadStateOut σ m where

/-- `get` without the requirements of `MonadStateOf`. -/
abbrev getState [MonadStateOut σ m] [GetState σ m] : m σ :=
  GetState.getState

abbrev getTheState (σ : Type u) [GetState σ m] : m σ :=
  getState

/-! ## Set State -/

class SetState (σ : semiOutParam $ Type u) (μ : Type v) where
  set (s : σ) : μ

instance (priority := low) [SetState σ μ] : StateOut σ μ where

abbrev MonadSetState (σ : semiOutParam $ Type u) (m : Type u → Type v) :=
  SetState σ (m PUnit)

/-- `set` generalized beyond monads to any imperative. -/
abbrev setState [StateOut σ μ] [SetState σ μ] (s : σ) : μ :=
  SetState.set s

abbrev setTheState (σ : Type u) [SetState σ μ] (s : σ) : μ :=
  setState s

/-! ## Modify State -/

class ModifyState (σ : semiOutParam $ Type u) (μ : Type v) where
  modify (f : σ → σ) : μ

instance (priority := low) [ModifyState σ μ] : StateOut σ μ where

abbrev MonadModifyState (σ : semiOutParam $ Type u) (m : Type u → Type v) :=
  ModifyState σ (m PUnit)

/-- `modify` generalized beyond monads to any imperative. -/
abbrev modifyState [StateOut σ μ] [ModifyState σ μ] (f :σ → σ) : μ :=
  ModifyState.modify (σ := σ) f

abbrev modifyTheState (σ : Type u) [ModifyState σ μ] (f :σ → σ) : μ :=
  modifyState (σ := σ) f

protected abbrev ModifyState.set [ModifyState σ μ] (s : σ) : μ :=
  modifyState fun _ => s

instance (priority := low) [ModifyState σ μ] : SetState σ μ := ⟨ModifyState.set⟩

/-! ## Modify State & Get Value -/

class ModifyGet (σ : semiOutParam $ Type u) (m : Type u → Type v) where
  modifyGet {α : Type u} : (σ → α × σ) → m α

protected abbrev ModifyGet.get [ModifyGet σ m] : m σ :=
  ModifyGet.modifyGet fun s => (s, s)

instance (priority := low) [ModifyGet σ m] : GetState σ m := ⟨ModifyGet.get⟩

protected abbrev ModifyGet.modify [ModifyGet σ m] (f : σ → σ) : m PUnit :=
  ModifyGet.modifyGet fun s => (⟨⟩, f s)

instance (priority := low) [ModifyGet σ m] : MonadModifyState σ m := ⟨ModifyGet.modify⟩

instance (priority := low) [GetState σ m] [MonadSetState σ m] [ModifyGet σ m] : MonadStateOf σ m where
  get := getState
  set := setState
  modifyGet := ModifyGet.modifyGet

@[simp] theorem get_eq_getState
  [GetState σ m] [MonadSetState σ m] [ModifyGet σ m] :
  (get : m σ) = getState
:= rfl

@[simp] theorem getState_eq_modifyGet [ModifyGet σ m] :
  (getState : m σ) = modifyGet fun s => (s, s)
:= rfl

@[simp] theorem set_eq_setState
  [GetState σ m] [MonadSetState σ m] [ModifyGet σ m] {s : σ} :
  (set s : m PUnit) = setState s
:= rfl

@[simp] theorem setState_eq_modifyGet [ModifyGet σ m] {s : σ} :
  (setState s : m PUnit) = modifyGet fun _ => (⟨⟩, s)
:= rfl

/-! ## Missing Core Lemmas for Lifting -/

@[simp] theorem read_eq_liftM [MonadLift m n] [MonadReaderOf ρ m] :
  (read : n ρ) = liftM (read : m ρ)
:= rfl

@[simp] theorem get_eq_liftM [MonadLift m n] [MonadStateOf σ m] :
  (get : n σ) = liftM (get : m σ)
:= rfl

@[simp] theorem set_eq_liftM [MonadLift m n] [MonadStateOf σ m] {s : σ} :
  (set s : n PUnit) = liftM (set s : m PUnit)
:= rfl

@[simp] theorem modifyGet_eq_liftM [MonadLift m n] [MonadStateOf σ m] {f : σ → α × σ} :
  (modifyGet f : n α) = liftM (modifyGet f : m α)
:= rfl

@[simp] theorem modify_eq_modifyGet [MonadState σ m] {f : σ → σ} :
  (modify f : m PUnit) = modifyGet fun s => (⟨⟩, f s)
:= rfl
