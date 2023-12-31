/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Data.Nat.Factorial.Basic

#align_import prereq.mathlib.data.nat.factorial.basic

/-!
# Stuff for data.nat.factorial.basic
-/


namespace Nat

theorem asc_le_pow_mul_factorial {s t : ℕ} : t.ascFactorial s ≤ s.factorial * (t + 1) ^ s := by
  induction' s with s ih
  · simp
  rw [ascFactorial_succ, factorial_succ, pow_succ', mul_mul_mul_comm]
  refine' Nat.mul_le_mul _ ih
  rw [add_comm t, add_one_mul s, mul_add_one s, add_assoc]
  simp

end Nat

