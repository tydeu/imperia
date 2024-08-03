/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.PrettyPrinter

namespace Imperia

/-! ## No-op -/

class Nop (μ : Type u) where
  nop : μ

export Nop (nop)

instance : Nop PUnit := ⟨⟨⟩⟩

@[simp] theorem nop_eq_unit : (nop : PUnit) = ⟨⟩ := rfl

instance [Pure m] : Nop (m PUnit) := ⟨pure ⟨⟩⟩

@[simp] theorem nop_eq_pure [Pure m] : (nop : m PUnit) = pure ⟨⟩ := rfl

/-! ## Return -/

class SetReturn (α : outParam $ Type u) (μ : Type v) where
  setReturn (a : α) : μ

export SetReturn (setReturn)

instance [Pure m] : SetReturn α (m α) := ⟨pure⟩
@[simp] theorem setReturn_eq_pure [Pure m] : (setReturn a : m α) = pure a := rfl

class Ret (α : outParam $ Type u) (μ  : Type u) where
  ret (a : α) : μ

export Ret (ret)

class Halt (μ  : Type u) where
  halt : μ

export Halt (halt)

/-! # Bind -/

class HBind (α : outParam $ Type u) (ξ : Type v) (μ : Type w) where
  hBind (x : ξ) (f : α → μ) : μ

export HBind (hBind)

@[default_instance] instance [HAndThen α β β] : HBind Unit α β := ⟨HAndThen.hAndThen⟩

class MBind (m : Type u → Type v) (μ : Type w) where
  bind (x : m α) (f : α → μ) : μ

@[default_instance] instance [MBind m μ] : HBind α (m α) μ := ⟨MBind.bind⟩

class MonadHBind (m : Type u₁ → Type v₁) (n : Type u₂ → Type v₂) where
  bind (x : m α) (f : α → n β) : n β

@[default_instance] instance [MonadHBind m n] : MBind m (n α) := ⟨MonadHBind.bind⟩

@[default_instance] instance [Bind m] : MonadHBind m m := ⟨Bind.bind⟩

/-! # AndThen -/

instance : AndThen PUnit := ⟨fun _ f => f ()⟩
instance : HAndThen PUnit.{u+1} PUnit.{v+1} PUnit.{v+1} := ⟨fun _ f => f ()⟩
