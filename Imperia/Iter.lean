/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Imperia.Cont
import Imperia.Actions.Iter

namespace Imperia

abbrev Iter μ α :=
  Cont (Cont μ Unit) α

class Iterable (μ : Type u) (ρ : Type v) (α : outParam $ Type w) where
  iter (r : ρ) : Iter μ α

export Iterable (iter)

instance : Iterable μ (Iter μ α) α := ⟨id⟩

namespace Iter

/-! ## Core Logic -/

@[inline] def done : Iter μ α :=
  fun _ done => done ()

@[simp] theorem app_done :
  done s d = d ()
:= rfl

instance : Halt (Cont (Iter μ α) Empty) := ⟨Cont.exec Iter.done⟩

@[simp] theorem app_halt :
  (halt : Cont (Iter μ α) Empty) = Cont.exec Iter.done
:= rfl

@[inline] def step (a : α) (f : Unit → Iter μ α) : Iter μ α :=
  fun step done => step a fun _ => f () step done

@[simp] theorem app_step :
  step a k s d = s a fun _ => k () s d
:= rfl

instance : Yield α (Cont (Iter μ α) Unit) := ⟨Iter.step⟩

@[simp] theorem app_yield :
  (yield a : Cont (Iter μ α) Unit) k = Iter.step a k
:= rfl

/-! ## Combinators -/

@[inline] def forM [Applicative m] (x : Iter (m PUnit) α) (f : α → m PUnit) : m PUnit :=
  x (fun c loop => f c *> loop ()) |>.run'

@[inline] def map (f : α → β) (x : Iter μ α) : Iter μ β :=
  fun step => x fun a => step (f a)

@[inline] def filter (f : α → Bool) (x : Iter μ α) : Iter μ α :=
  fun step => x fun a loop => if f a then step a loop else loop ()

@[inline] def filterMap (f : α → Option β) (x : Iter μ α) : Iter μ β :=
  fun step => x fun a? loop => if let some a := f a? then step a loop else loop ()

@[inline] def fold (f : β → α → β) (init : β) (x : Iter (β → β) α) : β :=
  x (fun a loop b => loop () (f b a)) (fun _ b => b) init

@[inline] def foldM [Monad m] (f : β → α → m β) (init : β) (x : Iter (β → m β) α) : m β :=
  x (fun a loop b => bind (f b a) fun b => loop () b) (fun _ b => pure b) init

@[inline] def toArray (x : Iter (Array α → Array α) α) : Array α :=
  x.fold Array.push Array.empty
