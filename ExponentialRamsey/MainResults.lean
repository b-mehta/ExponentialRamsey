/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Section12

/-!
# Summary of main results

In this file we demonstrate the main result of this formalisation, using the proofs which are
given fully in other files. The purpose of this file is to show the form in which the definitions
and theorem look.
-/


namespace MainResults

open SimpleGraph

open SimpleGraph.TopEdgeLabelling

/-- Since `fin t` denotes the numbers `{0, ..., t - 1}`, we can think of a function `fin t → ℕ`
as being a vector in `ℕ^t`, ie `n = (n₀, n₁, ..., nₜ₋₁)`.
Then `is_ramsey_valid (fin N) n` means that for any labelling `C` of the edges of the complete graph
on `{0, ..., N - 1}`, there is a finite subset `m` of this graph's vertices, and a label `i` such
that `|m| ≥ nᵢ`, and all edges between vertices in `m` are labelled `i`.
In the two-colour case discussed in the blogpost, we would have `t = 2`, and `n = (k, l)`.
In Lean this is denoted by `![k, l]`, as in the examples below.
-/
theorem ramsey_valid_iff {t N : ℕ} (n : Fin t → ℕ) :
    IsRamseyValid (Fin N) n =
      ∀ C : (completeGraph (Fin N)).edgeSetEmbedding → Fin t,
        ∃ m : Finset (Fin N), ∃ i : Fin t, MonochromaticOf C m i ∧ n i ≤ m.card :=
  rfl

/-- The ramsey number of the vector `n` is then just the infimum of all `N` such that
`is_ramsey_valid (fin N) n`.
-/
theorem ramseyNumber_def {t : ℕ} (n : Fin t → ℕ) :
    ramseyNumber n = sInf {N | IsRamseyValid (Fin N) n} :=
  (Nat.find_eq_iff _).2 ⟨csInf_mem (ramsey_fin_exists n), fun m => Nat.not_mem_of_lt_sInf⟩

-- We've got a definition of Ramsey numbers, let's first make sure it satisfies some of
-- the obvious properties.
example : ∀ k, ramseyNumber ![2, k] = k := by simp

example : ∀ k l, ramseyNumber ![k, l] = ramseyNumber ![l, k] :=
  ramseyNumber_pair_swap

-- It also satisfies the inductive bound by Erdős-Szekeres
theorem ramseyNumber_inductive_bound :
    ∀ k ≥ 2, ∀ l ≥ 2, ramseyNumber ![k, l] ≤ ramseyNumber ![k - 1, l] + ramseyNumber ![k, l - 1] :=
  fun _ h _ => ramseyNumber_two_colour_bound_aux h

-- And we can use this bound to get the standard upper bound in terms of the binomial coefficient,
-- which is written `n.choose k` in Lean.
theorem ramseyNumber_binomial_bound : ∀ k l, ramseyNumber ![k, l] ≤ (k + l - 2).choose (k - 1) :=
  ramseyNumber_le_choose

theorem ramseyNumber_power_bound : ∀ k, ramseyNumber ![k, k] ≤ 4 ^ k := fun _ =>
  diagonalRamsey_le_four_pow

-- We can also verify some small values:
example : ramseyNumber ![3, 3] = 6 :=
  ramseyNumber_three_three

example : ramseyNumber ![3, 4] = 9 :=
  ramseyNumber_three_four

example : ramseyNumber ![4, 4] = 18 :=
  ramseyNumber_four_four

-- The `![]` notation means the input to the `ramsey_number` function is a vector, and indeed gives
-- values for more than two colours too
example : ramseyNumber ![3, 3, 3] = 17 :=
  ramseyNumber_three_three_three

-- We also have Erdős' lower bound on Ramsey numbers
theorem ramseyNumber_lower_bound : ∀ k ≥ 2, Real.sqrt 2 ^ k ≤ ramseyNumber ![k, k] := fun _ =>
  diagonalRamsey_lower_bound_simpler

-- Everything up to this point has been known results, which were needed for the formalisation,
-- served as a useful warm up to the main result, and hopefully demonstrate the correctness
-- of the definition of Ramsey numbers.
-- Finally, the titular statement, giving an exponential improvement to the upper bound on Ramsey
-- numbers.
theorem exponential_ramsey_improvement : ∃ ε > 0, ∀ k, (ramseyNumber ![k, k] : ℝ) ≤ (4 - ε) ^ k :=
  global_bound

end MainResults

