/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Stuff for analysis.calculus.mean_value
-/


theorem Convex.strictMonoOn_of_hasDerivAt_pos {D : Set ℝ} (hD : Convex ℝ D) {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ D, HasDerivAt f (f' x) x) (hf' : ∀ x ∈ interior D, 0 < f' x) : StrictMonoOn f D :=
  by
  refine strictMonoOn_of_deriv_pos hD ?_ ?_
  · exact HasDerivAt.continuousOn hf
  intro x hx
  rw [HasDerivAt.deriv (hf x (interior_subset hx))]
  exact hf' x hx

theorem Convex.strictAntiOn_of_hasDerivAt_neg {D : Set ℝ} (hD : Convex ℝ D) {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ D, HasDerivAt f (f' x) x) (hf' : ∀ x ∈ interior D, f' x < 0) : StrictAntiOn f D :=
  by
  refine strictAntiOn_of_deriv_neg hD ?_ ?_
  · exact HasDerivAt.continuousOn hf
  intro x hx
  rw [HasDerivAt.deriv (hf x (interior_subset hx))]
  exact hf' x hx
