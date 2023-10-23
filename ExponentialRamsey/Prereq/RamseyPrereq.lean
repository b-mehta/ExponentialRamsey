/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ExponentialRamsey.Prereq.Mathlib.Algebra.BigOperators.Ring
import ExponentialRamsey.Prereq.Mathlib.Algebra.Order.Monoid.Lemmas
import ExponentialRamsey.Prereq.Mathlib.Combinatorics.SimpleGraph.Basic
import ExponentialRamsey.Prereq.Mathlib.Combinatorics.SimpleGraph.DegreeSum
import ExponentialRamsey.Prereq.Mathlib.Data.Nat.Choose.Basic
import ExponentialRamsey.Prereq.Mathlib.Data.Nat.Choose.Central
import ExponentialRamsey.Prereq.Mathlib.Data.Nat.Choose.Sum
import ExponentialRamsey.Prereq.Mathlib.Data.Nat.Factorial.Basic
import ExponentialRamsey.Prereq.Mathlib.Data.Fin.VecNotation

#align_import prereq.ramsey_prereq

/-!
# Misc prereqs and collect imports
-/


theorem Fin.ne_zero_iff_eq_one : ∀ {x : Fin 2}, x ≠ 0 ↔ x = 1 := by decide

theorem Fin.eq_zero_iff_ne_one : ∀ {x : Fin 2}, x = 0 ↔ x ≠ 1 := by decide

theorem Fin.fin_two_eq_zero_of_ne_one {x : Fin 2} (hx : x ≠ 1) : x = 0 := by
  rwa [Fin.eq_zero_iff_ne_one]

