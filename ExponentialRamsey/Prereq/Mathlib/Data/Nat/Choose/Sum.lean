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

-- choose_le_two_pow exists in Mathlib.Data.Nat.Choose.Bounds but is not well-named
theorem choose_le_two_pow' {n k : ℕ} : n.choose k ≤ 2 ^ n :=
  match le_or_gt k n with
  | Or.inl h => by
    rw [← sum_range_choose n]
    refine single_le_sum (fun _ _ => zero_le') ?_
    rwa [mem_range_succ_iff]
  | Or.inr h => by
    rw [choose_eq_zero_of_lt h]
    exact zero_le'

end Nat
