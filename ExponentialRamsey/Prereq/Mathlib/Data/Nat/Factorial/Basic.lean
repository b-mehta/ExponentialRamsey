/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Stuff for data.nat.factorial.basic
-/

namespace Nat


theorem asc_le_pow_mul_factorial {s t : ℕ} : t.ascFactorial s ≤ s.factorial * t ^ s :=
  match s with
  | 0 => by simp
  | n + 1 => by
    rcases t.eq_zero_or_pos with rfl | ht
    · simp [zero_ascFactorial]
    rw [ascFactorial_succ, factorial_succ, pow_succ', mul_mul_mul_comm]
    refine Nat.mul_le_mul ?_ asc_le_pow_mul_factorial
    rw [add_comm t, add_one_mul, Nat.add_le_add_iff_right]
    exact Nat.le_mul_of_pos_right _ ht

theorem asc_le_pow_mul_factorial' {s t : ℕ} : t.ascFactorial s ≤ s.factorial * t ^ s := by
  cases t
  case zero =>
    cases s
    case zero => simp
    case succ t => simp [zero_ascFactorial]
  case succ t => exact asc_le_pow_mul_factorial

-- theorem asc_le_pow_mul_factorial'' {s t : ℕ} : t.ascFactorial s ≤ s.factorial * t ^ s := by
theorem asc_le_pow_mul_factorial'' (t : ℕ) : (s : ℕ) → t.ascFactorial s ≤ s.factorial * t ^ s
  | 0 => by simp
  | 1 => by simp [ascFactorial_succ]
  | (s + 2) => by
      rw [ascFactorial_succ, factorial_succ, pow_succ', mul_mul_mul_comm]
      cases t
      · simp [zero_ascFactorial]
      · refine Nat.mul_le_mul ?_ (asc_le_pow_mul_factorial'' _ (s + 1))
        rw [add_comm, add_one_mul (s + 1), Nat.add_le_add_iff_right]
        exact Nat.le_mul_of_pos_right _ (succ_pos _)

end Nat
