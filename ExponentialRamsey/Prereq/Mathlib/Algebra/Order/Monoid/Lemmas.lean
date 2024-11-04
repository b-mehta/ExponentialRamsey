
/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic

/-!
# Stuff for Mathlib.Algebra.Order.Monoid.Unbundled.Basic
-/


@[to_additive]
theorem MulLECancellable.hMul {α : Type*} [LE α] [Semigroup α] {a b : α} (ha : MulLECancellable a)
    (hb : MulLECancellable b) : MulLECancellable (a * b) :=
  by
  intro x y h
  rw [mul_assoc, mul_assoc] at h
  exact hb (ha h)

@[to_additive]
theorem MulLECancellable.of_hMul_left {α : Type*} [LE α] [Semigroup α]
    [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} (hab : MulLECancellable (a * b)) :
    MulLECancellable b := by
  intro x y h
  apply hab
  rw [mul_assoc, mul_assoc]
  exact mul_le_mul_left' h a

