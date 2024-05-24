/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Algebra.Ring.Nat
import Mathlib.Data.Nat.Factorial.Basic

#align_import prereq.mathlib.data.nat.factorial.basic

/-!
# Stuff for data.nat.factorial.basic
-/

namespace Nat

theorem asc_le_pow_mul_factorial {s t : ℕ} : t.ascFactorial s ≤ s.factorial * t ^ s := by
  induction' s with s ih
  · simp
  rcases t.eq_zero_or_pos with rfl | ht
  · simp [zero_ascFactorial]
  rw [ascFactorial_succ, factorial_succ, pow_succ', mul_mul_mul_comm]
  refine' Nat.mul_le_mul _ ih
  rw [add_comm t, add_one_mul s, Nat.add_le_add_iff_right]
  exact Nat.le_mul_of_pos_right s ht

end Nat

