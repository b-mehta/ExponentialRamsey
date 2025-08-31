/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Stuff for analysis.calculus.iterated_deriv
-/


noncomputable section

open scoped Classical Topology BigOperators

open Filter Asymptotics Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

-- lemma iterated_deriv_within_univ {n : ℕ} {f : 𝕜 → F} {n : ℕ} :
--   iterated_deriv_within n f univ = iterated_deriv n f :=
theorem iteratedFDerivWithin_nhds {u : Set E} {x : E} {f : E → F} {n : ℕ} (hu : u ∈ 𝓝 x) :
    iteratedFDerivWithin 𝕜 n f u x = iteratedFDeriv 𝕜 n f x := by
  rw [← iteratedFDerivWithin_univ, ← univ_inter u, iteratedFDerivWithin_inter hu]

theorem iteratedDerivWithin_nhds {u : Set 𝕜} {x : 𝕜} {f : 𝕜 → F} {n : ℕ} (hu : u ∈ 𝓝 x) :
    iteratedDerivWithin n f u x = iteratedDeriv n f x := by
  rw [iteratedDerivWithin, iteratedDeriv, iteratedFDerivWithin_nhds hu]
