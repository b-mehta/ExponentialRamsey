/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Order.Interval.Set.Basic

/-!
# Stuff for analysis.calculus.taylor
-/


open Set

open scoped Nat

section

variable {α : Type*} [Lattice α]

/-- The unordered open-open interval. -/
def uIoo (x y : α) : Set α :=
  Ioo (x ⊓ y) (x ⊔ y)

theorem uIoo_of_le {x y : α} (h : x ≤ y) : uIoo x y = Ioo x y := by
  rw [uIoo, inf_eq_left.2 h, sup_eq_right.2 h]

theorem uIoo_of_ge {x y : α} (h : y ≤ x) : uIoo x y = Ioo y x := by
  rw [uIoo, inf_eq_right.2 h, sup_eq_left.2 h]

theorem uIoo_comm (x y : α) : uIoo x y = uIoo y x := by rw [uIoo, uIoo, inf_comm, sup_comm]

theorem uIoo_subset_Ioo {a₁ a₂ b₁ b₂ : α} (ha : a₁ ∈ Icc a₂ b₂) (hb : b₁ ∈ Icc a₂ b₂) :
    uIoo a₁ b₁ ⊆ Ioo a₂ b₂ :=
  Ioo_subset_Ioo (le_inf ha.1 hb.1) (sup_le ha.2 hb.2)

end

theorem taylor_mean_remainder_unordered {f : ℝ → ℝ} {g g' : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ} (hx : x₀ ≠ x)
    (hf : ContDiffOn ℝ n f (uIcc x₀ x))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (uIcc x₀ x)) (uIoo x₀ x))
    (gcont : ContinuousOn g (uIcc x₀ x))
    (gdiff : ∀ x_1 : ℝ, x_1 ∈ uIoo x₀ x → HasDerivAt g (g' x_1) x_1)
    (g'_ne : ∀ x_1 : ℝ, x_1 ∈ uIoo x₀ x → g' x_1 ≠ 0) :
    ∃ x' ∈ uIoo x₀ x,
      f x - taylorWithinEval f n (uIcc x₀ x) x₀ x =
        ((x - x') ^ n / n ! * (g x - g x₀) / g' x') •
          iteratedDerivWithin (n + 1) f (uIcc x₀ x) x' :=
  by
  rcases Ne.lt_or_lt hx with (hx₀ | hx₀)
  · rw [uIcc_of_le hx₀.le] at hf hf' gcont ⊢
    rw [uIoo_of_le hx₀.le] at g'_ne gdiff hf' ⊢
    exact taylor_mean_remainder hx₀ hf hf' gcont gdiff g'_ne
  rw [uIcc_of_ge hx₀.le] at hf hf' gcont ⊢
  rw [uIoo_of_ge hx₀.le] at g'_ne gdiff hf' ⊢
  rcases exists_ratio_hasDerivAt_eq_ratio_slope (fun t => taylorWithinEval f n (Icc x x₀) t x)
      (fun t => ((n ! : ℝ)⁻¹ * (x - t) ^ n) • iteratedDerivWithin (n + 1) f (Icc x x₀) t) hx₀
      (continuousOn_taylorWithinEval (uniqueDiffOn_Icc hx₀) hf)
      (fun _ hy => taylorWithinEval_hasDerivAt_Ioo x hx₀ hy hf hf') g g' gcont gdiff with
    ⟨y, hy, h⟩
  use y, hy
  -- The rest is simplifications and trivial calculations
  simp only [taylorWithinEval_self] at h
  rw [mul_comm, ← div_left_inj' (g'_ne y hy), mul_div_cancel_right₀ _ (g'_ne y hy)] at h
  rw [← neg_sub, ← h]
  field_simp [g'_ne y hy, n.factorial_ne_zero]
  ring

theorem taylor_mean_remainder_lagrange_unordered {f : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ} (hx : x₀ ≠ x)
    (hf : ContDiffOn ℝ n f (uIcc x₀ x))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (uIcc x₀ x)) (uIoo x₀ x)) :
    ∃ x' ∈ uIoo x₀ x,
      f x - taylorWithinEval f n (uIcc x₀ x) x₀ x =
        iteratedDerivWithin (n + 1) f (uIcc x₀ x) x' * (x - x₀) ^ (n + 1) / (n + 1)! := by
  have gcont : ContinuousOn (fun t : ℝ => (x - t) ^ (n + 1)) (uIcc x₀ x) := by
    refine Continuous.continuousOn ?_
    continuity
  have xy_ne : ∀ y : ℝ, y ∈ uIoo x₀ x → (x - y) ^ n ≠ 0 :=
    by
    intro y hy
    refine pow_ne_zero _ ?_
    rw [sub_ne_zero]
    cases' le_total x₀ x with h h
    · rw [uIoo_of_le h] at hy
      exact hy.2.ne'
    · rw [uIoo_of_ge h] at hy
      exact hy.1.ne
  have hg' : ∀ y : ℝ, y ∈ uIoo x₀ x → -(↑n + 1) * (x - y) ^ n ≠ 0 := fun y hy =>
    mul_ne_zero (neg_ne_zero.mpr (Nat.cast_add_one_ne_zero n)) (xy_ne y hy)
  -- We apply the general theorem with g(t) = (x - t)^(n+1)
  rcases taylor_mean_remainder_unordered hx hf hf' gcont (fun y _ => monomial_has_deriv_aux y x _)
      hg' with
    ⟨y, hy, h⟩
  use y, hy
  simp only [sub_self, zero_pow, Ne.eq_def, Nat.succ_ne_zero, not_false_iff, zero_sub, mul_neg] at h
  rw [h, neg_div, ← div_neg, neg_mul, neg_neg]
  field_simp [n.cast_add_one_ne_zero, n.factorial_ne_zero, xy_ne y hy]
  rw [← mul_assoc (n ! : ℝ), ← Nat.cast_add_one, ← Nat.cast_mul, mul_comm (n !), ← n.factorial_succ]
  ring


-- x' should be in uIoo x₀ x
theorem taylor_mean_remainder_central_aux {f : ℝ → ℝ} {g g' : ℝ → ℝ} {x₀ x a b : ℝ} {n : ℕ}
    (hab : a < b) (hx : x ∈ Icc a b) (hx₀ : x₀ ∈ Icc a b) (hf : ContDiffOn ℝ n f (Icc a b))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (Icc a b)) (Ioo a b))
    (gcont : ContinuousOn g (Icc a b)) (gdiff : ∀ y : ℝ, y ∈ Ioo a b → HasDerivAt g (g' y) y) :
    ∃ x' ∈ Ioo a b,
      x' ≠ x ∧
        (f x - taylorWithinEval f n (Icc a b) x₀ x) * g' x' =
          ((x - x') ^ n / n ! * (g x - g x₀)) • iteratedDerivWithin (n + 1) f (Icc a b) x' :=
  by
  rcases eq_or_ne x₀ x with (rfl | hx')
  · simp only [sub_self, taylorWithinEval_self, MulZeroClass.mul_zero, zero_div, zero_smul,
      eq_self_iff_true, exists_prop, and_true_iff, MulZeroClass.zero_mul]
    obtain ⟨x', hx'⟩ := ((Ioo_infinite hab).diff (Set.finite_singleton x₀)).nonempty
    exact ⟨x', by simpa using hx'⟩
  rcases Ne.lt_or_lt hx' with (hx' | hx')
  · have h₁ : Icc x₀ x ⊆ Icc a b := Icc_subset_Icc hx₀.1 hx.2
    have h₂ : Ioo x₀ x ⊆ Ioo a b := Ioo_subset_Ioo hx₀.1 hx.2
    obtain ⟨y, hy, h⟩ :=
      exists_ratio_hasDerivAt_eq_ratio_slope (fun t => taylorWithinEval f n (Icc a b) t x)
        (fun t => ((n ! : ℝ)⁻¹ * (x - t) ^ n) • iteratedDerivWithin (n + 1) f (Icc a b) t) hx'
        ((continuousOn_taylorWithinEval (uniqueDiffOn_Icc hab) hf).mono h₁)
        (fun _ hy => taylorWithinEval_hasDerivAt_Ioo _ hab (h₂ hy) hf hf') g g' (gcont.mono h₁)
        fun y hy => gdiff y (h₂ hy)
    refine ⟨y, h₂ hy, hy.2.ne, ?_⟩
    -- The rest is simplifications and trivial calculations
    simp only [taylorWithinEval_self] at h
    field_simp [← h, n.factorial_ne_zero]
    ring
  · have h₁ : Icc x x₀ ⊆ Icc a b := Icc_subset_Icc hx.1 hx₀.2
    have h₂ : Ioo x x₀ ⊆ Ioo a b := Ioo_subset_Ioo hx.1 hx₀.2
    obtain ⟨y, hy, h⟩ :=
      exists_ratio_hasDerivAt_eq_ratio_slope (fun t => taylorWithinEval f n (Icc a b) t x)
        (fun t => ((n ! : ℝ)⁻¹ * (x - t) ^ n) • iteratedDerivWithin (n + 1) f (Icc a b) t) hx'
        ((continuousOn_taylorWithinEval (uniqueDiffOn_Icc hab) hf).mono h₁)
        (fun _ hy => taylorWithinEval_hasDerivAt_Ioo _ hab (h₂ hy) hf hf') g g' (gcont.mono h₁)
        fun y hy => gdiff y (h₂ hy)
    refine ⟨y, h₂ hy, hy.1.ne', ?_⟩
    -- The rest is simplifications and trivial calculations
    simp only [taylorWithinEval_self] at h
    rw [← neg_sub, neg_mul, ← h]
    field_simp [n.factorial_ne_zero]
    ring

theorem taylor_mean_remainder_central {f : ℝ → ℝ} {g g' : ℝ → ℝ} {x₀ x a b : ℝ} {n : ℕ}
    (hab : a < b) (hx : x ∈ Icc a b) (hx₀ : x₀ ∈ Icc a b) (hf : ContDiffOn ℝ n f (Icc a b))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (Icc a b)) (Ioo a b))
    (gcont : ContinuousOn g (Icc a b)) (gdiff : ∀ y : ℝ, y ∈ Ioo a b → HasDerivAt g (g' y) y)
    (g'_ne : ∀ y : ℝ, y ∈ Ioo a b → g' y ≠ 0) :
    ∃ x' ∈ Ioo a b,
      f x - taylorWithinEval f n (Icc a b) x₀ x =
        ((x - x') ^ n / n ! * (g x - g x₀) / g' x') • iteratedDerivWithin (n + 1) f (Icc a b) x' :=
  by
  obtain ⟨y, hy, _, h⟩ := taylor_mean_remainder_central_aux hab hx hx₀ hf hf' gcont gdiff
  refine ⟨y, hy, ?_⟩
  rw [smul_eq_mul] at h
  rw [smul_eq_mul, div_mul_eq_mul_div, ← h, mul_div_cancel_right₀]
  exact g'_ne _ hy

theorem taylor_mean_remainder_lagrange_central {f : ℝ → ℝ} {x x₀ a b : ℝ} {n : ℕ} (hab : a < b)
    (hx : x ∈ Icc a b) (hx₀ : x₀ ∈ Icc a b) (hf : ContDiffOn ℝ n f (Icc a b))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (Icc a b)) (Ioo a b)) :
    ∃ x' ∈ Ioo a b,
      f x - taylorWithinEval f n (Icc a b) x₀ x =
        iteratedDerivWithin (n + 1) f (Icc a b) x' * (x - x₀) ^ (n + 1) / (n + 1)! :=
  by
  have gcont : ContinuousOn (fun t : ℝ => (x - t) ^ (n + 1)) (Icc a b) := by
    refine Continuous.continuousOn ?_; continuity
  rcases taylor_mean_remainder_central_aux hab hx hx₀ hf hf' gcont fun y _ =>
      monomial_has_deriv_aux y x _ with
    ⟨y, hy, hy', h⟩
  have hy_ne : x - y ≠ 0 := sub_ne_zero_of_ne hy'.symm
  use y, hy
  dsimp at h
  rw [← eq_div_iff] at h
  swap
  · exact mul_ne_zero (neg_ne_zero.2 (by positivity)) (by positivity)
  simp only [h, sub_self, zero_pow (Nat.succ_ne_zero n), zero_sub, mul_neg, neg_mul,
    Nat.factorial_succ, Nat.cast_add_one, neg_div_neg_eq, Nat.cast_mul, field_simps]
  rw [mul_left_comm, ← mul_assoc, ← div_div, div_eq_iff (pow_ne_zero _ hy_ne), div_mul_eq_mul_div]
  congr 1
  ring_nf

theorem taylor_mean_remainder_cauchy_central {f : ℝ → ℝ} {x x₀ a b : ℝ} {n : ℕ} (hab : a < b)
    (hx : x ∈ Icc a b) (hx₀ : x₀ ∈ Icc a b) (hf : ContDiffOn ℝ n f (Icc a b))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (Icc a b)) (Ioo a b)) :
    ∃ x' ∈ Ioo a b,
      f x - taylorWithinEval f n (Icc a b) x₀ x =
        iteratedDerivWithin (n + 1) f (Icc a b) x' * (x - x') ^ n / n ! * (x - x₀) :=
  by
  -- We apply the general theorem with g = id
  rcases taylor_mean_remainder_central hab hx hx₀ hf hf' continuousOn_id
      (fun _ _ => hasDerivAt_id _) fun _ _ => by simp with
    ⟨y, hy, h⟩
  refine ⟨y, hy, ?_⟩
  rw [h]
  field_simp [n.factorial_ne_zero]
  ring

theorem taylor_mean_remainder_bound_central {f : ℝ → ℝ} {a b C x x₀ : ℝ} {n : ℕ} (hab : a ≤ b)
    (hf : ContDiffOn ℝ (n + 1) f (Icc a b)) (hx : x ∈ Icc a b) (hx₀ : x₀ ∈ Icc a b)
    (hC : ∀ y ∈ Ioo a b, ‖iteratedDerivWithin (n + 1) f (Icc a b) y‖ ≤ C) :
    ‖f x - taylorWithinEval f n (Icc a b) x₀ x‖ ≤ C * |x - x₀| ^ (n + 1) / (n + 1)! :=
  by
  rcases eq_or_lt_of_le hab with (rfl | hab)
  · simp only [Icc_self, mem_singleton_iff] at hx hx₀
    substs hx₀ hx
    rw [taylorWithinEval_self, sub_self, sub_self, abs_zero, zero_pow (Nat.succ_ne_zero _),
      MulZeroClass.mul_zero, zero_div, norm_zero]
  have : DifferentiableOn ℝ (iteratedDerivWithin n f (Icc a b)) (Ioo a b) :=
    by
    refine
      (hf.differentiableOn_iteratedDerivWithin ?_ (uniqueDiffOn_Icc hab)).mono Ioo_subset_Icc_self
    rw [← Nat.cast_add_one, Nat.cast_lt]
    exact Nat.lt_succ_self _
  obtain ⟨x', hx', h⟩ := taylor_mean_remainder_lagrange_central hab hx hx₀ hf.of_succ this
  rw [h, norm_div, norm_mul, Real.norm_natCast, Real.norm_eq_abs ((x - x₀) ^ _), ← abs_pow]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_right (hC _ hx') (abs_nonneg _)

theorem exists_taylor_mean_remainder_bound_central {f : ℝ → ℝ} {a b x₀ : ℝ} {n : ℕ} (hab : a ≤ b)
    (hf : ContDiffOn ℝ (n + 1) f (Icc a b)) (hx₀ : x₀ ∈ Icc a b) :
    ∃ C, ∀ x ∈ Icc a b, ‖f x - taylorWithinEval f n (Icc a b) x₀ x‖ ≤ C * |x - x₀| ^ (n + 1) :=
  by
  rcases eq_or_lt_of_le hab with (rfl | h)
  · refine ⟨0, fun x hx => ?_⟩
    rw [Icc_self, mem_singleton_iff] at hx hx₀
    rw [hx₀, hx, taylorWithinEval_self, sub_self, MulZeroClass.zero_mul, norm_zero]
  let C := sSup ((fun y => ‖iteratedDerivWithin (n + 1) f (Icc a b) y‖) '' Icc a b)
  refine ⟨C / (n + 1)!, fun x hx => ?_⟩
  rw [div_mul_eq_mul_div]
  refine taylor_mean_remainder_bound_central hab hf hx hx₀ ?_
  intro y hy
  refine ContinuousOn.le_sSup_image_Icc (f := (‖iteratedDerivWithin (n + 1) f (Icc a b) ·‖))
     ?_ (Ioo_subset_Icc_self hy) -- Porting note: failed to infer the function f properly
  exact (hf.continuousOn_iteratedDerivWithin le_rfl (uniqueDiffOn_Icc h)).norm
