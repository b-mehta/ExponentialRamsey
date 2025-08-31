/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ExponentialRamsey.Prereq.Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Binary entropy function
Defines the function `h(p)` which gives the entropy of a Bernoulli random variable with probability
`p`. We define the function directly, since it is a useful function as is.
-/


open Real

/-- The binary entropy function -/
noncomputable def binEnt (b p : ℝ) : ℝ :=
  -p * logb b p - (1 - p) * logb b (1 - p)

@[simp]
theorem binEnt_zero {b : ℝ} : binEnt b 0 = 0 := by simp [binEnt]

theorem binEnt_symm {b p : ℝ} : binEnt b (1 - p) = binEnt b p := by
  rw [binEnt, sub_sub_cancel, binEnt]; ring

@[simp]
theorem binEnt_one {b : ℝ} : binEnt b 1 = 0 := by simp [binEnt]

theorem binEnt_nonneg {b p : ℝ} (hb : 1 < b) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) : 0 ≤ binEnt b p :=
  by
  have : ∀ x, 0 ≤ x → x ≤ 1 → 0 ≤ -(x * logb b x) :=
    by
    intro x hx₀ hx₁
    rw [Right.nonneg_neg_iff]
    exact mul_nonpos_of_nonneg_of_nonpos hx₀ (logb_nonpos hb hx₀ hx₁)
  rw [binEnt, sub_eq_add_neg, neg_mul]
  exact add_nonneg (this _ hp₀ hp₁) (this _ (sub_nonneg_of_le hp₁) (sub_le_self _ hp₀))

/-- An alternate expression for the binary entropy in terms of natural logs, which is sometimes
easier to prove analytic facts about. -/
theorem binEnt_eq {b p : ℝ} : binEnt b p = (-(p * log p) + -((1 - p) * log (1 - p))) / log b := by
  rw [binEnt, logb, logb, neg_mul, sub_eq_add_neg, add_div, mul_div_assoc', mul_div_assoc', neg_div,
    neg_div]

theorem binEnt_e {p : ℝ} : binEnt (exp 1) p = -p * log p - (1 - p) * log (1 - p) := by
  rw [binEnt, logb, logb, log_exp, div_one, div_one]

private theorem bin_ent_deriv_aux (x : ℝ) (hx₀ : x ≠ 0) (hx₁ : x ≠ 1) :
    HasDerivAt (fun y => -(y * log y) + -((1 - y) * log (1 - y))) (log (1 - x) - log x) x :=
  by
  have h : ∀ x : ℝ, x ≠ 0 → HasDerivAt (fun y => -(y * log y)) (-(log x + 1)) x :=
    by
    rintro x hx₀
    refine HasDerivAt.neg ?_
    have : 1 * log x + x * x⁻¹ = log x + 1 := by rw [one_mul, mul_inv_cancel₀ hx₀]
    rw [← this]
    exact HasDerivAt.mul (hasDerivAt_id' x) (hasDerivAt_log hx₀)
  suffices
    HasDerivAt (fun y => -(y * log y) + -((1 - y) * log (1 - y)))
      (-(log x + 1) + -(log (1 - x) + 1) * -1) x
    by
    convert this using 1
    ring_nf
  have : HasDerivAt (fun y : ℝ => 1 - y) (-1 : ℝ) x := (hasDerivAt_id' x).const_sub 1
  refine HasDerivAt.add (h _ hx₀) ?_
  exact (h (1 - x) (sub_ne_zero_of_ne hx₁.symm)).comp x ((hasDerivAt_id' x).const_sub 1)

