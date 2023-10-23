/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Data.Nat.Choose.Basic
import ExponentialRamsey.Prereq.Mathlib.Data.Nat.Factorial.Basic

#align_import prereq.mathlib.data.nat.choose.basic

/-!
# Stuff for data.nat.choose.basic
-/


namespace Nat

theorem choose_add_le_pow_left (s t : ℕ) : (s + t).choose s ≤ (t + 1) ^ s := by
  rw [add_comm, choose_eq_asc_factorial_div_factorial]
  exact Nat.div_le_of_le_mul asc_le_pow_mul_factorial

theorem choose_le_pow_left (s t : ℕ) : s.choose t ≤ (s + 1 - t) ^ t := by
  cases' le_or_lt t s with h h
  · obtain ⟨s, rfl⟩ := exists_add_of_le h
    refine (choose_add_le_pow_left t s).trans ?_
    rw [add_assoc, Nat.add_sub_cancel_left]
  rw [choose_eq_zero_of_lt h]
  exact zero_le'

end Nat

