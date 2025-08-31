/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Stuff for algebra.big_operators.ring
-/


open scoped BigOperators

theorem sum_tsub {α β : Type*} [AddCommMonoid β] [PartialOrder β] [ExistsAddOfLE β]
    [CovariantClass β β (· + ·) (· ≤ ·)] [ContravariantClass β β (· + ·) (· ≤ ·)] [Sub β]
    [OrderedSub β] (s : Finset α) {f g : α → β} (hfg : ∀ x ∈ s, g x ≤ f x) :
    ∑ x ∈ s, (f x - g x) = ∑ x ∈ s, f x - ∑ x ∈ s, g x :=
  eq_tsub_of_add_eq <| by
    rw [← Finset.sum_add_distrib];
    exact Finset.sum_congr rfl fun x hx => tsub_add_cancel_of_le <| hfg _ hx
