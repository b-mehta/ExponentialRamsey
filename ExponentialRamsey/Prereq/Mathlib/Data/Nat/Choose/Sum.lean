/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Data.Nat.Choose.Sum

/-!
# Stuff for data.nat.choose.sum
-/


namespace Nat

open Finset

theorem choose_le_two_pow {n k : ℕ} : n.choose k ≤ 2 ^ n := by
  cases' le_or_lt k n with h h
  · rw [← sum_range_choose n]
    refine single_le_sum (fun _ _ => zero_le') ?_
    rwa [mem_range_succ_iff]
  rw [choose_eq_zero_of_lt h]
  exact zero_le'

end Nat

