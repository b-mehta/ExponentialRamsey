/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Section8
import Prereq.Mathlib.Analysis.SpecialFunctions.Log.Base

#align_import section9

/-!
# Section 9
-/


namespace SimpleGraph

open scoped BigOperators ExponentialRamsey Nat Real

open Filter Finset Nat Real Asymptotics

-- fails at n = 0 because rhs is 0 and lhs is 1
theorem little_o_stirling :
    ∃ f : ℕ → ℝ,
      (f =o[atTop] fun i => (1 : ℝ)) ∧
        ∀ n : ℕ, n ≠ 0 → (n ! : ℝ) = (1 + f n) * sqrt (2 * π * n) * (n / exp 1) ^ n :=
  by
  refine' ⟨fun n => Stirling.stirlingSeq n / sqrt π - 1, _, _⟩
  · rw [is_o_one_iff]
    convert (stirling.tendsto_stirling_seq_sqrt_pi.div_const _).sub_const _ using 1
    rw [nhds_eq_nhds_iff, div_self, sub_self]
    rw [sqrt_ne_zero']
    exact pi_pos
  intro n hn
  rw [add_sub_cancel'_right, div_mul_eq_mul_div, mul_div_assoc, ← sqrt_div' _ pi_pos.le, ←
    div_mul_eq_mul_div, mul_div_cancel _ pi_pos.ne', Stirling.stirlingSeq, mul_assoc,
    div_mul_cancel]
  positivity

-- giving explicit bounds here requires an explicit version of stirling
theorem weak_little_o_stirling :
    ∃ f : ℕ → ℝ,
      (f =o[atTop] fun i => (i : ℝ)) ∧ ∀ᶠ n : ℕ in atTop, (n ! : ℝ) = 2 ^ f n * (n / exp 1) ^ n :=
  by
  obtain ⟨f, hf, hf'⟩ := little_o_stirling
  rw [is_o_one_iff] at hf
  refine' ⟨fun n => (log 2)⁻¹ * (log (1 + f n) + (1 / 2 * log (2 * π) + 1 / 2 * log n)), _, _⟩
  · refine' is_o.const_mul_left _ _
    refine' is_o.add _ _
    · refine'
        is_O.trans_is_o _ ((is_o_const_id_at_top (1 : ℝ)).comp_tendsto tendsto_nat_cast_atTop_atTop)
      -- show log (1 + o(1)) is O(1) (it's actually o(1) but O(1) is easier for now)
      rw [is_O_iff]
      refine' ⟨log 2, _⟩
      have h₁ : (-1 / 2 : ℝ) < 0 := by norm_num
      filter_upwards [eventually_gt_at_top 0, hf.eventually (eventually_ge_nhds h₁),
        hf.eventually (eventually_le_nhds zero_lt_one)] with n hn1 hneg h1
      have : 0 < 1 + f n := by linarith only [hneg]
      simp only [norm_eq_abs, Pi.const_one, Pi.one_apply, norm_one, mul_one]
      rw [abs_le, ← log_inv, ← one_div]
      refine' ⟨log_le_log_of_le (by norm_num1) _, log_le_log_of_le this (by linarith only [h1])⟩
      linarith only [hneg]
    suffices (fun n : ℝ => 1 / 2 * log (2 * π) + 1 / 2 * log n) =o[at_top] id by
      exact is_o.comp_tendsto this tendsto_nat_cast_atTop_atTop
    exact is_o.add (is_o_const_id_at_top _) (is_o_log_id_at_top.const_mul_left _)
  have h₁ : (-1 : ℝ) < 0 := by norm_num
  have := pi_pos
  filter_upwards [eventually_gt_at_top 0, hf.eventually (eventually_gt_nhds h₁),
    hf.eventually (eventually_le_nhds zero_lt_one)] with n hn1 hneg h1
  have : 0 < 1 + f n := by linarith only [hneg]
  rw [hf' n hn1.ne', rpow_def_of_pos, mul_inv_cancel_left₀ (log_pos one_lt_two).ne', ← mul_add, ←
    log_mul, ← log_rpow, ← sqrt_eq_rpow, ← log_mul, exp_log]
  all_goals positivity

-- g is log 2 - log k
theorem nine_four_log_aux :
    ∃ g : ℕ → ℝ,
      (g =o[atTop] fun i => (i : ℝ)) ∧
        ∀ᶠ l : ℕ in atTop, ∀ k, l ≤ k → g k ≤ log (k + l) - log k - log l :=
  by
  refine' ⟨fun k => log 2 - log k, _, _⟩
  · suffices (fun k : ℝ => log 2 - log k) =o[at_top] id by
      exact this.comp_tendsto tendsto_nat_cast_atTop_atTop
    exact is_o.sub (is_o_const_id_at_top _) is_o_log_id_at_top
  filter_upwards [eventually_gt_at_top 0] with l hl₀ k hlk
  rw [sub_sub, add_comm (log _), ← sub_sub, sub_le_sub_iff_right, ← log_div]
  · refine' log_le_log_of_le zero_lt_two _
    rwa [le_div_iff, two_mul, add_le_add_iff_right, Nat.cast_le]
    rwa [Nat.cast_pos]
  · positivity
  · positivity

theorem nine_four_aux_aux {f : ℕ → ℝ} (hf : f =o[atTop] fun i => (1 : ℝ)) :
    ∀ᶠ l : ℕ in atTop, ∀ k, l ≤ k → 2 ^ (-3 : ℝ) ≤ (1 + f (k + l)) / ((1 + f k) * (1 + f l)) :=
  by
  rw [is_o_one_iff] at hf
  have h₁ : (-1 / 2 : ℝ) < 0 := by norm_num
  filter_upwards [eventually_gt_at_top 0, top_adjuster (hf.eventually (eventually_ge_nhds h₁)),
    top_adjuster (hf.eventually (eventually_le_nhds zero_lt_one))] with l hn1 hneg h1 k hlk
  have h₂ : ∀ k, l ≤ k → 1 / 2 ≤ 1 + f k := by
    intro k hlk
    linarith only [hneg k hlk]
  have h₃ : ∀ k, l ≤ k → 1 + f k ≤ 2 := by
    intro k hlk
    linarith only [h1 k hlk]
  have h₄ : ∀ k, l ≤ k → 0 < 1 + f k := by
    intro k hlk
    linarith only [h₂ k hlk]
  refine'
    (div_le_div (h₄ _ le_add_self).le (h₂ _ le_add_self) (mul_pos (h₄ _ hlk) (h₄ _ le_rfl))
          (mul_le_mul (h₃ _ hlk) (h₃ _ le_rfl) (h₄ _ le_rfl).le zero_lt_two.le)).trans'
      _
  norm_num

-- f is -3 + (log 2 - log k - log (2 π)) / (2 log 2)
--    = -3 - (log k + log π) / (2 log 2)
theorem nine_four_aux :
    ∃ f : ℕ → ℝ,
      (f =o[atTop] fun i => (i : ℝ)) ∧
        ∀ᶠ l : ℕ in atTop,
          ∀ k,
            l ≤ k →
              (2 : ℝ) ^ f k * ((k + l) ^ (k + l) / (k ^ k * l ^ l)) ≤ ((k + l).choose l : ℝ) :=
  by
  obtain ⟨f, hf, hf'⟩ := little_o_stirling
  obtain ⟨g, hg, hg'⟩ := nine_four_log_aux
  refine' ⟨fun k => -3 + (2 * log 2)⁻¹ * (g k - log (2 * π)), _, _⟩
  · refine' is_o.add (is_o.comp_tendsto (is_o_const_id_at_top _) tendsto_nat_cast_atTop_atTop) _
    refine' is_o.const_mul_left _ _
    exact is_o.sub hg (is_o.comp_tendsto (is_o_const_id_at_top _) tendsto_nat_cast_atTop_atTop)
  filter_upwards [top_adjuster (eventually_gt_at_top 0), nine_four_aux_aux hf, hg'] with l hk₀ h₈
    hg'' k hlk
  have := pi_pos
  have hl₀' := hk₀ l le_rfl
  have hk₀' := hk₀ k hlk
  rw [← Nat.choose_symm_add, Nat.cast_add_choose, hf', hf' _ hk₀'.ne', hf' _ (hk₀ l le_rfl).ne',
    mul_mul_mul_comm, ← div_mul_div_comm, mul_mul_mul_comm, ← div_mul_div_comm, div_pow, div_pow,
    div_pow, div_mul_div_comm _ (exp 1 ^ k), ← pow_add,
    div_div_div_cancel_right (_ : ℝ) (pow_ne_zero _ (exp_pos _).ne'), Nat.cast_add, ← sqrt_mul, ←
    sqrt_div, rpow_add two_pos, mul_assoc (2 * π), mul_div_mul_left]
  rotate_left
  · positivity
  · positivity
  · positivity
  · positivity
  refine' mul_le_mul_of_nonneg_right _ (by positivity)
  refine'
    mul_le_mul (h₈ k hlk) _ (rpow_nonneg_of_nonneg two_pos.le _) ((h₈ k hlk).trans' (by norm_num1))
  rw [← le_logb_iff_rpow_le one_lt_two, logb, log_sqrt, log_div, @log_mul k, @log_mul _ l, div_div,
    add_left_comm, add_comm (log _), ← sub_sub, ← sub_sub, div_eq_mul_inv, mul_comm]
  ·
    exact
      div_le_div_of_le_of_nonneg (sub_le_sub_right (hg'' _ hlk) _)
        (mul_nonneg two_pos.le (log_nonneg one_le_two))
  · positivity
  · positivity
  · positivity
  · positivity
  · positivity
  · positivity
  · positivity
  · positivity

-- f is -3 + (log 2 - log k - log (2 π)) / (2 log 2)
theorem nine_four :
    ∃ f : ℕ → ℝ,
      (f =o[atTop] fun i => (i : ℝ)) ∧
        ∀ᶠ l : ℕ in atTop,
          ∀ k,
            l ≤ k →
              ∀ γ : ℝ,
                γ = l / (k + l) →
                  (2 : ℝ) ^ f k * γ ^ (-l : ℝ) * (1 - γ) ^ (-k : ℝ) ≤ ((k + l).choose l : ℝ) :=
  by
  obtain ⟨f, hf, hf'⟩ := nine_four_aux
  refine' ⟨f, hf, _⟩
  filter_upwards [top_adjuster (eventually_gt_at_top 0), hf'] with l hk₀ hf₁ k hlk γ hγ
  have := hk₀ k hlk
  refine' (hf₁ k hlk).trans_eq' _
  rw [mul_assoc, hγ, one_sub_div, add_sub_cancel, rpow_neg, rpow_neg, ← inv_rpow, ← inv_rpow,
    inv_div, inv_div, rpow_nat_cast, rpow_nat_cast, mul_comm (_ ^ l), div_pow, div_pow,
    div_mul_div_comm, ← pow_add]
  all_goals positivity

theorem end_ramseyNumber (μ₀ μ₁ p₀ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ,
            μ₀ ≤ μ →
              μ ≤ μ₁ →
                ∀ n : ℕ,
                  ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                    (¬∃ (m : Finset (Fin n)) (c : Fin 2),
                          χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                      ∀ ini : BookConfig χ,
                        p₀ ≤ ini.p →
                          (endState μ k l ini).X.card ≤
                            ramseyNumber ![k, ⌈(l : ℝ) ^ (3 / 4 : ℝ)⌉₊] :=
  by
  filter_upwards [one_div_k_lt_p μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀, top_adjuster (eventually_gt_at_top 0)] with l
    hl hl₀ k hlk μ hμl hμu n χ hχ ini hini
  refine' (condition_fails_at_end (hl₀ k hlk).ne' (hl₀ l le_rfl).ne').resolve_right _
  rw [not_le]
  exact hl k hlk μ hμl hμu n χ hχ ini hini _ le_rfl

theorem end_ramsey_number_pow_isLittleO :
    ∃ f : ℕ → ℝ,
      (f =o[atTop] fun i => (i : ℝ)) ∧
        ∀ μ₀ μ₁ p₀ : ℝ,
          0 < μ₀ →
            μ₁ < 1 →
              0 < p₀ →
                ∀ᶠ l : ℕ in atTop,
                  ∀ k,
                    l ≤ k →
                      ∀ μ,
                        μ₀ ≤ μ →
                          μ ≤ μ₁ →
                            ∀ n : ℕ,
                              ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                                (¬∃ (m : Finset (Fin n)) (c : Fin 2),
                                      χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                                  ∀ ini : BookConfig χ,
                                    p₀ ≤ ini.p → ((endState μ k l ini).X.card : ℝ) ≤ 2 ^ f k :=
  by
  refine' ⟨fun k => (log 2)⁻¹ * (2 * (log k * k ^ (3 / 4 : ℝ))), _, _⟩
  · refine' is_o.const_mul_left _ _
    refine' is_o.const_mul_left _ _
    suffices (fun k => log k * k ^ (3 / 4 : ℝ)) =o[at_top] id by
      exact this.comp_tendsto tendsto_nat_cast_atTop_atTop
    refine'
      (is_o.mul_is_O (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4))
            (is_O_refl _ _)).congr'
        eventually_eq.rfl _
    filter_upwards [eventually_gt_at_top (0 : ℝ)] with k hk
    rw [← rpow_add hk]
    norm_num1
    rw [rpow_one, id.def]
  intro μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀
  filter_upwards [end_ramsey_number μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀, eventually_ge_at_top 1] with l hl hl₁ k
    hlk μ hμl hμu n χ hχ ini hini
  specialize hl k hlk μ hμl hμu n χ hχ ini hini
  rw [rpow_def_of_pos two_pos, mul_inv_cancel_left₀ (log_pos one_lt_two).ne', mul_left_comm, ←
    rpow_def_of_pos (Nat.cast_pos.2 _)]
  swap
  · exact hl₁.trans hlk
  rw [ramsey_number_pair_swap] at hl
  refine' (Nat.cast_le.2 (hl.trans ramsey_number_le_right_pow_left')).trans _
  rw [Nat.cast_pow, ← rpow_nat_cast]
  refine' rpow_le_rpow_of_exponent_le (Nat.one_le_cast.2 (hl₁.trans hlk)) _
  refine'
    (ceil_le_two_mul _).trans
      (mul_le_mul_of_nonneg_left
        (rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.2 hlk) (by norm_num1)) two_pos.le)
  exact (one_le_rpow (Nat.one_le_cast.2 hl₁) (by norm_num1)).trans' (by norm_num1)

theorem descFactorial_eq_prod {n k : ℕ} : n.descFactorial k = ∏ i in range k, (n - i) :=
  by
  induction k
  · simp
  rw [Nat.descFactorial_succ, k_ih, Finset.prod_range_succ, mul_comm]

theorem cast_descFactorial_eq_prod {n k : ℕ} :
    (n.descFactorial k : ℝ) = ∏ i in range k, (n - i : ℝ) := by
  rw [desc_factorial_eq_prod, prod_range_cast_nat_sub]

theorem pow_div_le_choose {n k : ℕ} (h : k ≤ n) : (n / k : ℝ) ^ k ≤ n.choose k :=
  by
  rw [Nat.choose_eq_descFactorial_div_factorial, Nat.cast_div, ← prod_range_add_one_eq_factorial,
    Nat.cast_prod, ← prod_range_reflect, cast_desc_factorial_eq_prod, ← prod_div_distrib]
  · suffices ∀ x ∈ range k, (n / k : ℝ) ≤ (n - x : ℝ) / (k - 1 - x + 1 : ℕ)
      by
      refine' (Finset.prod_le_prod _ this).trans_eq' _
      · intros
        positivity
      simp
    intro x hx
    rw [mem_range] at hx
    have : 0 < k - x := Nat.sub_pos_of_lt hx
    rw [Nat.sub_sub, add_comm 1, ← Nat.sub_sub, Nat.sub_add_cancel, div_le_div_iff,
      Nat.cast_sub hx.le, mul_sub, sub_mul, sub_le_sub_iff_left, mul_comm, ← Nat.cast_mul, ←
      Nat.cast_mul, Nat.cast_le]
    · exact Nat.mul_le_mul_right _ h
    · rw [Nat.cast_pos]
      exact pos_of_gt hx
    · rwa [Nat.cast_pos]
    · exact this
  · exact Nat.factorial_dvd_descFactorial _ _
  · positivity

theorem exp_le_one_sub_inv {x : ℝ} (hx : x < 1) : exp x ≤ (1 - x)⁻¹ :=
  by
  rw [le_inv (exp_pos _) (sub_pos_of_lt hx), ← Real.exp_neg, ← neg_add_eq_sub]
  exact add_one_le_exp _

theorem le_of_gamma_le_half {l k : ℕ} {γ : ℝ} (h : γ = l / (k + l)) (hl : 0 < l) (hγ : γ ≤ 1 / 2) :
    l ≤ k :=
  by
  rwa [h, div_le_div_iff, one_mul, mul_comm, two_mul, add_le_add_iff_right, Nat.cast_le] at hγ
  · exact lt_add_of_le_of_pos (Nat.cast_nonneg k) (Nat.cast_pos.2 hl)
  · exact two_pos

theorem nine_three_lower_n (γ₀ : ℝ) (hγ₀ : 0 < γ₀) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k : ℕ,
        ∀ γ : ℝ,
          γ = l / (k + l) →
            γ₀ ≤ γ →
              γ < 1 →
                l ≤ k →
                  ∀ δ : ℝ, δ ≤ γ / 20 → ∀ n : ℕ, exp (-δ * k) * (k + l).choose l ≤ n → 2 ≤ n :=
  by
  filter_upwards [eventually_gt_at_top 0, eventually_ge_at_top ⌈log 2 / (γ₀ * (19 / 20))⌉₊] with l
    hl hk k γ hγ hγl hγ₁ hlk δ hδ n hn
  have : (1 - γ)⁻¹ ^ (k : ℕ) ≤ (k + l).choose l :=
    by
    rw [add_comm, Nat.choose_symm_add]
    refine' (pow_div_le_choose (by simp)).trans_eq' _
    rw [hγ, one_sub_div, add_sub_cancel, inv_div, add_comm, Nat.cast_add]
    positivity
  have : exp γ ^ k ≤ (k + l).choose l :=
    by
    refine' this.trans' (pow_le_pow_of_le_left (exp_pos _).le _ _)
    exact exp_le_one_sub_inv hγ₁
  rw [← @Nat.cast_le ℝ, Nat.cast_two]
  refine' hn.trans' ((mul_le_mul_of_nonneg_left this (exp_pos _).le).trans' _)
  rw [mul_comm (-δ), ← exp_nat_mul, ← Real.exp_add, ← mul_add, neg_add_eq_sub, ←
    log_le_iff_le_exp two_pos]
  have : γ₀ * (19 / 20) ≤ γ - δ := by linarith
  refine' (mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)).trans' _
  rw [← div_le_iff, ← Nat.ceil_le]
  · exact hk.trans hlk
  positivity

theorem ge_floor {n : ℝ} (h : 1 ≤ n) : (n / 2 : ℝ) ≤ ⌊(n : ℝ)⌋₊ :=
  by
  cases' lt_or_le n 2 with h₂ h₂
  · have : (1 : ℝ) ≤ ⌊n⌋₊ := by rwa [Nat.one_le_cast, Nat.one_le_floor_iff]
    refine' this.trans' _
    linarith
  refine' (Nat.sub_one_lt_floor n).le.trans' _
  linarith

theorem nine_three_part_one :
    ∃ f : ℕ → ℝ,
      (f =o[atTop] fun i => (i : ℝ)) ∧
        ∀ γ₀ : ℝ,
          0 < γ₀ →
            ∀ᶠ l : ℕ in atTop,
              ∀ k : ℕ,
                ∀ γ : ℝ,
                  γ = l / (k + l) →
                    γ₀ ≤ γ →
                      γ ≤ 1 / 5 →
                        l ≤ k →
                          ∀ δ : ℝ,
                            δ = min (1 / 200) (γ / 20) →
                              ∀ n : ℕ,
                                ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                                  (¬∃ (m : Finset (Fin n)) (c : Fin 2),
                                        χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                                    ∀ ini : BookConfig χ,
                                      1 / 4 ≤ ini.p →
                                        ⌊(n / 2 : ℝ)⌋₊ ≤ ini.X.card →
                                          exp (-δ * k) * (k + l).choose l ≤ n →
                                            exp (-δ * k) *
                                                  (1 - γ) ^ (-k + (redSteps γ k l ini).card : ℝ) *
                                                (beta γ k l ini / γ) ^
                                                  (densitySteps γ k l ini).card ≤
                                              2 ^ f k :=
  by
  have hμ₁ : (1 / 5 : ℝ) < 1 := by norm_num1
  have hp₀ : (0 : ℝ) < 1 / 4 := by norm_num1
  obtain ⟨f₁, hf₁, hf₁'⟩ := end_ramsey_number_pow_is_o
  obtain ⟨f₂, hf₂, hf₂'⟩ := seven_one (1 / 5) hμ₁
  obtain ⟨f₃, hf₃, hf₃'⟩ := nine_four
  refine' ⟨fun k => f₁ k - f₂ k - f₃ k + 2, _, _⟩
  · refine' is_o.add ((hf₁.sub hf₂).sub hf₃) _
    exact (is_o_const_id_at_top _).comp_tendsto tendsto_nat_cast_atTop_atTop
  intro γ₀ hγ₀
  specialize hf₁' γ₀ (1 / 5) (1 / 4) hγ₀ hμ₁ hp₀
  specialize hf₂' γ₀ (1 / 4) hγ₀ hp₀
  filter_upwards [hf₁', hf₂', hf₃', nine_three_lower_n γ₀ hγ₀,
    beta_pos γ₀ (1 / 5) (1 / 4) hγ₀ hμ₁ hp₀] with l hfk hgk hc hn'' hβ k γ hγ hγl hγu hlk δ hδ n χ
    hχ ini hini hn' hn
  clear hf₁' hf₂' hf₃'
  have hδ' : δ ≤ γ / 20 := by
    rw [hδ]
    exact min_le_right _ _
  specialize hfk k hlk γ hγl hγu n χ hχ ini hini
  specialize hgk k hlk γ hγl hγu n χ hχ ini hini
  specialize hc k hlk γ hγ
  specialize hn'' k γ hγ hγl (hγu.trans_lt (by norm_num1)) hlk δ hδ' n hn
  specialize hβ k hlk γ hγl hγu n χ ini hini
  have hγ₁ : γ < 1 := by linarith only [hγu]
  have hγ₁' : 0 < 1 - γ := sub_pos_of_lt hγ₁
  have hγ₀' : 0 < γ := hγ₀.trans_le hγl
  have : 2 ^ (-2 : ℝ) * (n : ℝ) ≤ ini.X.card :=
    by
    refine' (Nat.cast_le.2 hn').trans' ((ge_floor _).trans_eq' _)
    · rw [one_le_div (zero_lt_two' ℝ)]
      exact_mod_cast hn''
    rw [div_div, div_eq_mul_inv, mul_comm]
    norm_num
  have h₅ :
    0 <
      2 ^ f₂ k * γ ^ l * (1 - γ) ^ (red_steps γ k l ini).card *
        (beta γ k l ini / γ) ^ (density_steps γ k l ini).card :=
    by positivity
  replace hn := hn.trans' (mul_le_mul_of_nonneg_left hc (exp_pos _).le)
  replace hgk := (mul_le_mul_of_nonneg_left this h₅.le).trans hgk
  rw [← mul_assoc] at hgk
  replace hgk := (mul_le_mul_of_nonneg_left hn (mul_nonneg h₅.le (by norm_num1))).trans hgk
  replace hgk := hgk.trans hfk
  rw [sub_add, sub_sub, sub_eq_add_neg (f₁ k), rpow_add two_pos]
  refine' (mul_le_mul_of_nonneg_right hgk (rpow_pos_of_pos two_pos _).le).trans' _
  simp only [mul_assoc, mul_left_comm _ (exp (-δ * k))]
  refine' mul_le_mul_of_nonneg_left _ (exp_pos _).le
  simp only [mul_left_comm _ ((_ / γ) ^ _)]
  rw [mul_comm]
  refine' mul_le_mul_of_nonneg_left _ (by positivity)
  simp only [mul_left_comm _ ((1 - γ) ^ (_ : ℝ))]
  rw [rpow_add hγ₁']
  refine' mul_le_mul_of_nonneg_left _ (by positivity)
  simp only [mul_left_comm _ (γ ^ (_ : ℝ))]
  simp only [mul_left_comm _ (γ ^ (_ : ℕ))]
  rw [rpow_neg hγ₀'.le, rpow_nat_cast, rpow_nat_cast, mul_inv_cancel_left₀ (pow_pos hγ₀' _).ne',
    mul_left_comm]
  refine' le_mul_of_one_le_right (pow_nonneg hγ₁'.le _) _
  rw [← rpow_add two_pos, ← rpow_add two_pos, ← rpow_add two_pos]
  simp only [← add_assoc, neg_add, neg_sub]
  ring_nf
  rw [rpow_zero]

theorem nine_three_part_two :
    ∃ f : ℕ → ℝ,
      (f =o[atTop] fun i => (i : ℝ)) ∧
        ∀ γ₀ : ℝ,
          0 < γ₀ →
            ∀ᶠ l : ℕ in atTop,
              ∀ k : ℕ,
                ∀ γ : ℝ,
                  γ = l / (k + l) →
                    γ₀ ≤ γ →
                      γ ≤ 1 / 5 →
                        l ≤ k →
                          ∀ δ : ℝ,
                            δ = min (1 / 200) (γ / 20) →
                              ∀ n : ℕ,
                                ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                                  (¬∃ (m : Finset (Fin n)) (c : Fin 2),
                                        χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                                    ∀ ini : BookConfig χ,
                                      1 / 4 ≤ ini.p →
                                        ⌊(n / 2 : ℝ)⌋₊ ≤ ini.X.card →
                                          exp (-δ * k) * (k + l).choose l ≤ n →
                                            γ * (k - (redSteps γ k l ini).card) ≤
                                              beta γ k l ini * (redSteps γ k l ini).card / (1 - γ) *
                                                    log (γ / beta γ k l ini) +
                                                  δ * k +
                                                f k :=
  by
  have hμ₁ : (1 / 5 : ℝ) < 1 := by norm_num1
  have hp₀ : (0 : ℝ) < 1 / 4 := by norm_num1
  obtain ⟨f, hf, hf'⟩ := nine_three_part_one
  refine' ⟨fun k => log 2 * f k + 7 / (1 - 1 / 5) * (k ^ (15 / 16 : ℝ) * (3 * log k)), _, _⟩
  · clear hf'
    refine' is_o.add (is_o.const_mul_left hf _) _
    refine' is_o.const_mul_left _ _
    suffices (fun k : ℝ => k ^ (15 / 16 : ℝ) * (3 * log k)) =o[at_top] id by
      exact this.comp_tendsto tendsto_nat_cast_atTop_atTop
    simp only [mul_left_comm _ (3 : ℝ)]
    refine' is_o.const_mul_left _ _
    simp only [mul_comm _ (log _)]
    refine'
      ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 16)).mul_isBigO
            (is_O_refl _ _)).congr'
        eventually_eq.rfl _
    filter_upwards [eventually_gt_at_top (0 : ℝ)] with k hk
    rw [← rpow_add hk]
    norm_num
  intro γ₀ hγ₀
  filter_upwards [hf' γ₀ hγ₀, eight_five γ₀ (1 / 5) (1 / 4) hγ₀ hμ₁ hp₀,
    top_adjuster (eventually_gt_at_top 0), beta_le_μ γ₀ (1 / 5) (1 / 4) hγ₀ hμ₁ hp₀,
    beta_pos γ₀ (1 / 5) (1 / 4) hγ₀ hμ₁ hp₀, one_div_sq_le_beta γ₀ (1 / 5) (1 / 4) hγ₀ hμ₁ hp₀] with
    l h₁ h₈₅ hk₀ hβμ hβ₀ hβk k γ hγ hγl hγu hlk δ hδ n χ hχ ini hini hn' hn
  clear hf'
  specialize h₁ k γ hγ hγl hγu hlk δ hδ n χ hχ ini hini hn' hn
  specialize h₈₅ k hlk γ hγl hγu n χ hχ ini hini
  specialize hβμ k hlk γ hγl hγu n χ ini hini
  specialize hβ₀ k hlk γ hγl hγu n χ ini hini
  specialize hβk k hlk γ hγl hγu n χ ini hini
  have hγ₁ : γ < 1 := by linarith only [hγu]
  have hγ₀' : 0 < γ := hγ₀.trans_le hγl
  have :
    exp (γ * (k - (red_steps γ k l ini).card)) ≤ (1 - γ) ^ (-k + (red_steps γ k l ini).card : ℝ) :=
    by
    rw [exp_mul, neg_add_eq_sub, ← neg_sub (k : ℝ), rpow_neg (sub_nonneg_of_le hγ₁.le), ←
      inv_rpow (sub_nonneg_of_le hγ₁.le)]
    refine' rpow_le_rpow (exp_pos _).le (exp_le_one_sub_inv hγ₁) (sub_nonneg_of_le _)
    rw [Nat.cast_le]
    exact four_four_red _ hχ _
  rw [mul_right_comm] at h₁
  clear hn hδ hχ hini hn' hγ
  replace h₁ := (mul_le_mul_of_nonneg_left this (by positivity)).trans h₁
  rw [neg_mul, Real.exp_neg, ← inv_div, inv_pow, ← mul_inv, inv_mul_eq_div, div_le_iff, ←
    le_log_iff_exp_le, log_mul, log_mul, log_exp, log_pow, log_rpow two_pos, mul_comm (f k)] at h₁
  rotate_left
  · positivity
  · positivity
  · positivity
  · positivity
  · positivity
  · positivity
  refine' h₁.trans _
  rw [add_rotate, add_left_comm, add_assoc, add_assoc, add_le_add_iff_left, add_le_add_iff_left]
  have : 0 ≤ log (γ / beta γ k l ini) :=
    by
    refine' log_nonneg _
    rwa [one_le_div hβ₀]
  refine' (mul_le_mul_of_nonneg_right h₈₅ this).trans _
  rw [add_comm, add_mul, div_mul_eq_mul_div _ (1 - γ), mul_assoc (beta γ k l ini / _),
    div_mul_eq_mul_div (beta γ k l ini), ← mul_assoc, ← mul_assoc]
  refine' add_le_add _ _
  swap
  · refine' div_le_div_of_le_left (mul_nonneg (by positivity) this) (sub_pos_of_lt hγ₁) _
    exact sub_le_sub_left hβμ _
  refine' mul_le_mul_of_nonneg_left _ (by positivity)
  rw [log_div hγ₀'.ne' hβ₀.ne', bit1, add_comm, one_add_mul, sub_eq_add_neg]
  refine' add_le_add (log_le_log_of_le hγ₀' _) _
  · refine' hγ₁.le.trans _
    rw [Nat.one_le_cast]
    exact hk₀ k hlk
  rw [← Nat.cast_two, ← log_pow, neg_le, ← log_inv, ← one_div]
  refine' log_le_log_of_le _ hβk
  specialize hk₀ k hlk
  positivity

theorem hMul_log_ineq {x : ℝ} (hx : 0 < x) : -x * log x ≤ exp (-1) :=
  by
  have := add_one_le_exp (-log x - 1)
  rwa [sub_add_cancel, sub_eq_add_neg, Real.exp_add, Real.exp_neg, exp_log hx, inv_mul_eq_div,
    le_div_iff hx, mul_comm, mul_neg, ← neg_mul] at this

theorem hMul_log_ineq_special {c x : ℝ} (hc : 0 < c) (hx : 0 < x) : x * log (c / x) ≤ c / exp 1 :=
  by
  have := mul_log_ineq (div_pos hx hc)
  rwa [neg_mul, ← mul_neg, ← log_inv, inv_div, div_mul_eq_mul_div, div_le_iff hc, Real.exp_neg,
    inv_mul_eq_div] at this

theorem nine_three_part_three (γ₀ : ℝ) (hγ₀ : 0 < γ₀) :
    ∃ f : ℕ → ℝ,
      (f =o[atTop] fun i => (i : ℝ)) ∧
        ∀ᶠ l : ℕ in atTop,
          ∀ k : ℕ,
            ∀ γ : ℝ,
              γ = l / (k + l) →
                γ₀ ≤ γ →
                  γ ≤ 1 / 5 →
                    l ≤ k →
                      ∀ δ : ℝ,
                        δ = min (1 / 200) (γ / 20) →
                          ∀ n : ℕ,
                            ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                              (¬∃ (m : Finset (Fin n)) (c : Fin 2),
                                    χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                                ∀ ini : BookConfig χ,
                                  1 / 4 ≤ ini.p →
                                    ⌊(n / 2 : ℝ)⌋₊ ≤ ini.X.card →
                                      exp (-δ * k) * (k + l).choose l ≤ n →
                                        (k : ℝ) * (1 - δ / γ) * (1 + 1 / (exp 1 * (1 - γ)))⁻¹ +
                                            f k ≤
                                          (redSteps γ k l ini).card :=
  by
  have hμ₁ : (1 / 5 : ℝ) < 1 := by norm_num1
  have hp₀ : (0 : ℝ) < 1 / 4 := by norm_num1
  obtain ⟨f, hf, hf'⟩ := nine_three_part_two
  refine' ⟨fun k => -(1 / γ₀ * |f k|), _, _⟩
  · rw [is_o_neg_left]
    refine' is_o.const_mul_left _ _
    exact hf.abs_left
  filter_upwards [hf' γ₀ hγ₀, beta_pos γ₀ _ _ hγ₀ hμ₁ hp₀] with l hl hβ k γ hγ hγl hγu hlk δ hδ n χ
    hχ ini hini hn' hn
  clear hf'
  specialize hl k γ hγ hγl hγu hlk δ hδ n χ hχ ini hini hn' hn
  specialize hβ k hlk γ hγl hγu n χ ini hini
  have hγ₀' : 0 < γ := hγ₀.trans_le hγl
  have hγ₁' : γ < 1 := hγu.trans_lt (by norm_num)
  rw [mul_div_assoc, mul_right_comm, add_assoc, ← sub_le_iff_le_add] at hl
  replace hl :=
    hl.trans
      (mul_le_mul_of_nonneg_right (mul_log_ineq_special hγ₀' hβ)
        (div_nonneg (Nat.cast_nonneg _) (sub_pos_of_lt hγ₁').le))
  have : 0 ≤ 1 / (exp 1 * (1 - γ)) := by
    rw [one_div]
    exact inv_nonneg_of_nonneg (mul_nonneg (exp_pos _).le (sub_pos_of_lt hγ₁').le)
  rw [mul_div_assoc', ← div_mul_eq_mul_div, div_div, mul_sub, sub_sub, add_comm, ← sub_sub,
    sub_le_iff_le_add, ← add_mul, div_eq_mul_inv, ← mul_add_one, ← one_div, add_comm _ (1 : ℝ), ←
    div_le_iff', ← div_div, sub_div, div_eq_mul_inv, mul_div_cancel_left, add_div, mul_comm δ,
    mul_div_assoc, ← sub_sub, ← mul_one_sub, sub_mul, div_mul_eq_mul_div, mul_div_assoc] at hl
  · refine' hl.trans' (sub_le_sub_left _ _)
    rw [mul_comm (1 / γ₀)]
    refine' mul_le_mul (le_abs_self _) (div_le_div zero_le_one _ hγ₀ hγl) _ (abs_nonneg _)
    · exact inv_le_one (le_add_of_nonneg_right this)
    refine' div_nonneg _ hγ₀'.le
    positivity
  · exact hγ₀'.ne'
  · positivity

theorem it_keeps_showing_up {γ : ℝ} (hγ : γ ≤ 1) : 0 < 1 + 1 / (exp 1 * (1 - γ)) :=
  add_pos_of_pos_of_nonneg zero_lt_one
    (one_div_nonneg.2 (mul_nonneg (exp_pos _).le (sub_nonneg_of_le hγ)))

theorem rearranging_more {c γ : ℝ} (hγl : 0.1 ≤ γ) (hγu : γ ≤ 0.2) (hc : 0 < c) (hc' : c < 0.95) :
    c < (1 - 1 / (200 * γ)) * (1 + 1 / (exp 1 * (1 - γ)))⁻¹ ↔
      1 / ((1 - 1 / (200 * γ)) / c - 1) / (1 - γ) < exp 1 :=
  by
  have hγ₀ : 0 < γ := hγl.trans_lt' (by norm_num1)
  have hγ₁ : γ < 1 := hγu.trans_lt (by norm_num1)
  rw [← div_eq_mul_inv, lt_div_iff (it_keeps_showing_up hγ₁.le), ← lt_div_iff' hc, ←
    lt_sub_iff_add_lt', one_div_lt, ← div_lt_iff (sub_pos_of_lt hγ₁)]
  · exact mul_pos (exp_pos _) (sub_pos_of_lt hγ₁)
  rw [sub_pos, lt_div_iff hc, one_mul]
  refine' hc'.trans_le _
  rw [le_sub_comm, ← div_div, div_le_iff hγ₀, ← div_le_iff']
  · exact hγl.trans' (by norm_num1)
  norm_num1

theorem numerics_one_middle_aux {γ : ℝ} (hγu : γ = 1 / 10) :
    0.67435 < (1 - 1 / 20) * (1 + 1 / (exp 1 * (1 - γ)))⁻¹ :=
  by
  subst hγu
  rw [← div_lt_iff', lt_inv _ (it_keeps_showing_up _), ← lt_sub_iff_add_lt', one_div_lt, ←
    div_lt_iff]
  · refine' exp_one_gt_d9.trans_le' _
    norm_num1
  · norm_num1
  · exact mul_pos (exp_pos _) (by norm_num1)
  all_goals norm_num1

theorem numerics_one_left {γ δ : ℝ} (hγl : 0 < γ) (hγu : γ ≤ 1 / 10) (hδ : δ = γ / 20) :
    0.67435 < (1 - δ / γ) * (1 + 1 / (exp 1 * (1 - γ)))⁻¹ :=
  by
  rw [hδ, div_div, mul_comm (20 : ℝ), ← div_div, div_self hγl.ne']
  refine' (numerics_one_middle_aux rfl).trans_le _
  refine' mul_le_mul_of_nonneg_left _ (by norm_num1)
  refine' inv_le_inv_of_le (it_keeps_showing_up (by linarith only [hγu])) _
  refine' add_le_add_left (one_div_le_one_div_of_le (mul_pos (exp_pos _) (by norm_num1)) _) _
  refine' mul_le_mul_of_nonneg_left _ (exp_pos _).le
  linarith only [hγu]

theorem ConcaveOn.hMul {f g : ℝ → ℝ} {s : Set ℝ} (hf : ConcaveOn ℝ s f) (hg : ConcaveOn ℝ s g)
    (hf' : MonotoneOn f s) (hg' : AntitoneOn g s) (hf'' : ∀ x ∈ s, 0 ≤ f x)
    (hg'' : ∀ x ∈ s, 0 ≤ g x) : ConcaveOn ℝ s fun x => f x * g x :=
  by
  refine' LinearOrder.concaveOn_of_lt hf.1 _
  intro x hx y hy hxy a b ha hb hab
  replace hg := hg.2 hx hy ha.le hb.le hab
  refine'
    (mul_le_mul (hf.2 hx hy ha.le hb.le hab) hg
          (add_nonneg (smul_nonneg ha.le (hg'' _ hx)) (smul_nonneg hb.le (hg'' _ hy)))
          (hf'' _ (hf.1 hx hy ha.le hb.le hab))).trans'
      _
  have : b = 1 - a := by rwa [eq_sub_iff_add_eq']
  subst this
  simp only [smul_eq_mul]
  suffices 0 ≤ a * (1 - a) * (g x - g y) * (f y - f x) by nlinarith only [this]
  exact
    mul_nonneg (mul_nonneg (by positivity) (sub_nonneg_of_le (hg' hx hy hxy.le)))
      (sub_nonneg_of_le (hf' hx hy hxy.le))

-- lemma convex_on_sub_const {s : set ℝ} {c : ℝ} (hs : convex ℝ s) : concave_on ℝ s (λ x, x - c) :=
-- (convex_on_id hs).sub (concave_on_const _ hs)
theorem ConvexOn.const_hMul {c : ℝ} {s : Set ℝ} {f : ℝ → ℝ} (hf : ConvexOn ℝ s f) (hc : 0 ≤ c) :
    ConvexOn ℝ s fun x => c * f x :=
  ⟨hf.1, fun x hx y hy a b ha hb hab =>
    (mul_le_mul_of_nonneg_left (hf.2 hx hy ha hb hab) hc).trans_eq
      (by simp only [smul_eq_mul] <;> ring_nf)⟩

theorem ConcaveOn.const_hMul {c : ℝ} {s : Set ℝ} {f : ℝ → ℝ} (hf : ConcaveOn ℝ s f) (hc : 0 ≤ c) :
    ConcaveOn ℝ s fun x => c * f x :=
  ⟨hf.1, fun x hx y hy a b ha hb hab =>
    (mul_le_mul_of_nonneg_left (hf.2 hx hy ha hb hab) hc).trans_eq'
      (by simp only [smul_eq_mul] <;> ring_nf)⟩

theorem StrictConvexOn.const_hMul_neg {c : ℝ} {s : Set ℝ} {f : ℝ → ℝ} (hf : StrictConvexOn ℝ s f)
    (hc : c < 0) : StrictConcaveOn ℝ s fun x => c * f x :=
  ⟨hf.1, fun x hx y hy hxy a b ha hb hab =>
    (mul_lt_mul_of_neg_left (hf.2 hx hy hxy ha hb hab) hc).trans_eq'
      (by simp only [smul_eq_mul] <;> ring_nf)⟩

theorem StrictConvexOn.const_hMul {c : ℝ} {s : Set ℝ} {f : ℝ → ℝ} (hf : StrictConvexOn ℝ s f)
    (hc : 0 < c) : StrictConvexOn ℝ s fun x => c * f x :=
  ⟨hf.1, fun x hx y hy hxy a b ha hb hab =>
    (mul_lt_mul_of_pos_left (hf.2 hx hy hxy ha hb hab) hc).trans_eq
      (by simp only [smul_eq_mul] <;> ring_nf)⟩

theorem convexOn_inv : ConvexOn ℝ (Set.Ioi (0 : ℝ)) fun x => x⁻¹ :=
  ConvexOn.congr' (convexOn_zpow (-1)) (by simp)

theorem convexOn_one_div : ConvexOn ℝ (Set.Ioi (0 : ℝ)) fun x => 1 / x :=
  ConvexOn.congr' (convexOn_zpow (-1)) (by simp)

theorem quadratic_is_concave {a b c : ℝ} (ha : 0 < a) :
    StrictConvexOn ℝ Set.univ fun x => a * x ^ 2 + b * x + c :=
  by
  have : ∀ x, a * x ^ 2 + b * x + c = a * (x + b / (2 * a)) ^ 2 - (a * (b / (2 * a)) ^ 2 - c) :=
    by
    intro x
    rw [← sub_add, ← mul_sub, add_left_inj, add_sq, add_sub_cancel, mul_add, mul_div_assoc',
      mul_div_assoc', mul_assoc, mul_left_comm, ← mul_assoc, mul_div_cancel_left, mul_comm x]
    exact mul_ne_zero (by positivity) ha.ne'
  simp only [this]
  refine' StrictConvexOn.sub_concaveOn _ (concaveOn_const _ convex_univ)
  refine' strict_convex_on.const_mul _ ha
  simpa using (Even.strictConvexOn_pow even_two two_pos.ne').translate_left (b / (2 * a))

theorem rearranging {c γ : ℝ} (hγ₀ : 0 < γ) (hγu : γ ≤ 0.2) :
    c < (1 - 1 / (200 * γ)) * (1 + 1 / (exp 1 * (1 - γ)))⁻¹ ↔
      (1 - c) * γ ^ 2 + (c * (1 + 1 / exp 1) - (1 + 1 / 200)) * γ + 1 / 200 < 0 :=
  by
  have hγ₁ : γ < 1 := hγu.trans_lt (by norm_num1)
  rw [← div_eq_mul_inv, ← div_div, one_sub_div hγ₀.ne', ← div_div,
    one_add_div (sub_pos_of_lt hγ₁).ne', div_div_eq_mul_div, div_mul_eq_mul_div, div_div,
    sub_add_eq_add_sub, sub_mul, mul_one_sub, mul_one_sub, lt_div_iff, mul_sub, sub_sub,
    add_sub_assoc', ← sub_add, sub_add_eq_add_sub, ← one_add_mul, mul_sub, lt_sub_iff_add_lt,
    mul_left_comm, sub_eq_add_neg, ← neg_mul, add_assoc, ← add_assoc (-c * _), ← add_one_mul,
    neg_add_eq_sub, ← sub_neg, add_comm, ← sq, ← add_sub, mul_comm γ, ← sub_mul, add_right_comm]
  refine' mul_pos hγ₀ (sub_pos_of_lt (hγ₁.trans_le (le_add_of_nonneg_right _)))
  rw [one_div_nonneg]
  exact (exp_pos _).le

-- lhs is 39/40 * (1 + 5 / (4 e))
theorem numerics_one {γ δ : ℝ} (hγl : 0 < γ) (hγu : γ ≤ 1 / 5) (hδ : δ = min (1 / 200) (γ / 20)) :
    0.6678 < (1 - δ / γ) * (1 + 1 / (exp 1 * (1 - γ)))⁻¹ :=
  by
  cases' le_total γ 0.1 with hγl' hγl'
  · refine' (numerics_one_left hγl hγl' _).trans_le' (by norm_num1)
    rw [hδ, min_eq_right_iff]
    refine' (div_le_div_of_le (by norm_num1) hγl').trans_eq _
    norm_num1
  rw [hδ, min_eq_left, div_div]
  swap
  · linarith only [hγl']
  rw [rearranging hγl hγu]
  set c : ℝ := 0.6678 with hc'
  let f : ℝ → ℝ := fun x => (1 - c) * x ^ 2 + (c * (1 + 1 / exp 1) - (1 + 1 / 200)) * x + 1 / 200
  have hc : 0 < 1 - c := by rw [hc']; norm_num
  have hf : StrictConvexOn ℝ Set.univ f := quadratic_is_concave hc
  change f γ < 0
  have hfive : (1 / 10 : ℝ) ≤ 1 / 5 := hγl'.trans hγu
  have h₁ : f (1 / 10) < 0 := by
    rw [← rearranging _ hfive]
    convert (numerics_one_middle_aux rfl).trans_le' _ using 3
    · norm_num1
    · norm_num1
    · norm_num1
  have h₂ : f (1 / 5) < 0 :=
    by
    rw [← rearranging (hγl.trans_le hγu) le_rfl, hc', rearranging_more hfive le_rfl]
    · refine' exp_one_gt_d9.trans_le' _
      norm_num1
    · norm_num1
    · norm_num1
  have : ConvexOn ℝ (Set.Icc (1 / 10 : ℝ) (1 / 5)) f :=
    hf.convex_on.subset (Set.subset_univ _) (convex_Icc _ _)
  have hγ : γ ∈ segment ℝ (1 / 10 : ℝ) (1 / 5) :=
    by
    rw [segment_eq_Icc hfive]
    exact ⟨hγl', hγu⟩
  have := ConvexOn.le_on_segment this _ _ hγ
  rotate_left
  · rwa [Set.left_mem_Icc]
  · rwa [Set.right_mem_Icc]
  refine' this.trans_lt _
  rw [max_lt_iff]
  exact ⟨h₁, h₂⟩

theorem nine_three (γ₀ : ℝ) (hγ₀ : 0 < γ₀) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k : ℕ,
        l ≤ k →
          ∀ γ : ℝ,
            γ = l / (k + l) →
              γ₀ ≤ γ →
                γ ≤ 1 / 5 →
                  ∀ δ : ℝ,
                    δ = min (1 / 200) (γ / 20) →
                      ∀ n : ℕ,
                        ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                          (¬∃ (m : Finset (Fin n)) (c : Fin 2),
                                χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                            ∀ ini : BookConfig χ,
                              1 / 4 ≤ ini.p →
                                ⌊(n / 2 : ℝ)⌋₊ ≤ ini.X.card →
                                  exp (-δ * k) * (k + l).choose l ≤ n →
                                    (2 / 3 : ℝ) * k ≤ (redSteps γ k l ini).card :=
  by
  obtain ⟨f, hf, hf'⟩ := nine_three_part_three γ₀ hγ₀
  have := hf.bound (by norm_num1 : (0 : ℝ) < 1e-3)
  filter_upwards [hf', top_adjuster (eventually_gt_at_top 0),
    top_adjuster (hf.bound (by norm_num1 : (0 : ℝ) < 1e-3))] with l h9 hk₀ herr k hlk γ hγ hγl hγu δ
    hδ n χ hχ ini hini hn' hn
  clear hf'
  have hl₀ : 0 < l := hk₀ l le_rfl
  specialize h9 k γ hγ hγl hγu hlk δ hδ n χ hχ ini hini hn' hn
  specialize herr k hlk
  rw [norm_eq_abs, norm_coe_nat, abs_le] at herr
  refine' h9.trans' _
  rw [mul_rotate]
  refine' (add_le_add_left herr.1 _).trans' _
  rw [← neg_mul, ← add_mul]
  refine' mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  linarith only [numerics_one (hγ₀.trans_le hγl) hγu hδ]

theorem yael_two {n k a : ℕ} : n.ascFactorial (k + a) = (n + a).ascFactorial k * n.ascFactorial a :=
  by
  induction' a with a ih
  · simp
  rw [Nat.add_succ, Nat.ascFactorial_succ, Nat.ascFactorial_succ, mul_left_comm, ← mul_assoc,
    Nat.add_succ n a, Nat.succ_ascFactorial (n + a), ih, mul_assoc, add_comm k a, ← add_assoc]

theorem asc_hMul_asc {a b c : ℕ} :
    a.ascFactorial b * (a + b).ascFactorial c = a.ascFactorial c * (a + c).ascFactorial b := by
  rw [mul_comm, ← yael_two, mul_comm, ← yael_two, add_comm]

theorem asc_div_asc_const_right' {a b c : ℕ} :
    (a.ascFactorial b : ℝ) / (a + c).ascFactorial b = a.ascFactorial c / (a + b).ascFactorial c :=
  by
  rw [div_eq_div_iff, ← Nat.cast_mul, asc_mul_asc, Nat.cast_mul]
  · positivity
  · positivity

theorem asc_div_asc_const_right {a b c : ℕ} :
    ((a + c).ascFactorial b : ℝ) / a.ascFactorial b = (a + b).ascFactorial c / a.ascFactorial c :=
  by
  rw [div_eq_div_iff, mul_comm, ← Nat.cast_mul, asc_mul_asc, Nat.cast_mul, mul_comm]
  · positivity
  · positivity

-- d = a + c
-- a = d - c
theorem asc_div_asc_const_right_sub' {b c d : ℕ} (h : c ≤ d) :
    ((d - c).ascFactorial b : ℝ) / d.ascFactorial b =
      (d - c).ascFactorial c / (d - c + b).ascFactorial c :=
  by
  obtain ⟨a, rfl⟩ := exists_add_of_le h
  rw [add_tsub_cancel_left, add_comm, asc_div_asc_const_right']

theorem choose_ratio {l k t : ℕ} (h : t ≤ k) :
    ((k + l - t).choose l : ℝ) / (k + l).choose l = ∏ i : ℕ in range t, (k - i) / (k + l - i) :=
  by
  rw [Nat.choose_eq_descFactorial_div_factorial, Nat.choose_eq_descFactorial_div_factorial,
    Nat.cast_div_div_div_cancel_right, ← tsub_add_eq_add_tsub h,
    Nat.add_descFactorial_eq_ascFactorial, Nat.add_descFactorial_eq_ascFactorial,
    asc_div_asc_const_right_sub' h, ← Nat.add_descFactorial_eq_ascFactorial, Nat.sub_add_cancel h, ←
    Nat.add_descFactorial_eq_ascFactorial, tsub_add_eq_add_tsub h, Nat.sub_add_cancel,
    cast_desc_factorial_eq_prod, cast_desc_factorial_eq_prod, ← prod_div_distrib]
  · simp
  · exact le_add_right h
  · exact Nat.factorial_dvd_descFactorial _ _
  · exact Nat.factorial_dvd_descFactorial _ _

theorem fact_d_two_part_one {l k t : ℕ} (h : t ≤ k) :
    ((k + l - t).choose l : ℝ) / (k + l).choose l =
      (k / (k + l)) ^ t * ∏ i in range t, (1 - i * l / (k * (k + l - i))) :=
  by
  have : ((k : ℝ) / (k + l)) ^ t = ∏ i in range t, k / (k + l) := by simp
  rw [this, choose_ratio h, ← prod_mul_distrib]
  refine' prod_congr rfl _
  intro i hi
  rw [mem_range] at hi
  have hik : i < k := hi.trans_le h
  have : 0 < k := pos_of_gt hik
  have : 0 < k - i := Nat.sub_pos_of_lt hik
  rw [one_sub_div, mul_div_assoc', div_mul_eq_mul_div, mul_div_assoc, mul_div_mul_left, mul_sub,
    mul_comm _ (i : ℝ), sub_sub, ← mul_add, ← sub_mul, mul_div_cancel]
  · positivity
  · positivity
  rw [← sub_add_eq_add_sub, ← Nat.cast_sub hik.le]
  positivity

theorem fact_d_two_part_two {l k t : ℕ} (h : t ≤ k) :
    ∏ i in range t, (1 - i * l / (k * (k + l - i)) : ℝ) ≤
      exp (-l / (k * (k + l)) * ∑ i in range t, i) :=
  by
  rw [mul_sum, Real.exp_sum]
  refine' Finset.prod_le_prod _ _
  · intro i hi
    rw [mem_range] at hi
    have hik : i < k := hi.trans_le h
    have : 0 < k := pos_of_gt hik
    have : 0 < k - i := Nat.sub_pos_of_lt hik
    rw [sub_nonneg, ← sub_add_eq_add_sub, ← Nat.cast_sub hik.le]
    refine' div_le_one_of_le _ (by positivity)
    rw [← Nat.cast_add, ← Nat.cast_mul, ← Nat.cast_mul, Nat.cast_le]
    exact Nat.mul_le_mul hik.le (Nat.le_add_left _ _)
  intro i hi
  rw [mem_range] at hi
  refine' (add_one_le_exp _).trans' _
  rw [neg_div, neg_mul, neg_add_eq_sub, sub_le_sub_iff_left, mul_comm, mul_div_assoc']
  have hik : i < k := hi.trans_le h
  have : 0 < k := pos_of_gt hik
  have : 0 < k - i := Nat.sub_pos_of_lt hik
  refine' div_le_div_of_le_left (by positivity) _ (mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _))
  · rw [← sub_add_eq_add_sub, ← Nat.cast_sub hik.le]
    positivity
  simp

theorem d_two {l k t : ℕ} {γ : ℝ} (ht : 0 < k) (h : t ≤ k) (hγ : γ = l / (k + l)) :
    ((k + l - t).choose l : ℝ) ≤
      exp (-γ * (t * (t - 1)) / (2 * k)) * (1 - γ) ^ t * (k + l).choose l :=
  by
  have hγ₀ : 0 ≤ γ := by rw [hγ]; positivity
  have hγ₁ : γ ≤ 1 := by rw [hγ]; refine' div_le_one_of_le (by simp) (by positivity)
  rw [← div_le_iff, fact_d_two_part_one h]
  swap
  · rw [Nat.cast_pos]
    exact Nat.choose_pos (Nat.le_add_left _ _)
  rw [mul_comm, hγ, one_sub_div, add_sub_cancel]
  swap
  · positivity
  refine' mul_le_mul_of_nonneg_right ((fact_d_two_part_two h).trans _) (by positivity)
  rw [exp_le_exp, ← div_div _ (2 : ℝ), mul_div_assoc, ← div_mul_eq_mul_div, neg_div, neg_div,
    div_div, neg_mul, neg_mul, mul_comm (k : ℝ), neg_le_neg_iff, ← Nat.cast_sum, sum_range_id, ←
    Nat.choose_two_right, Nat.cast_choose_two]

theorem nine_six :
    ∀ (l k t : ℕ) (γ : ℝ),
      0 < k →
        t ≤ k →
          γ = l / (k + l) →
            exp (-1) * (1 - γ) ^ (-t : ℝ) * exp (γ * t ^ 2 / (2 * k)) * (k + l - t).choose l ≤
              (k + l).choose l :=
  by
  intro l k t γ hk htk hγ
  have hγ₀ : 0 ≤ γ := by rw [hγ]; positivity
  have hγ₁ : γ < 1 := by
    rw [hγ, div_lt_one]
    · simpa only [lt_add_iff_pos_left, Nat.cast_pos] using hk
    · positivity
  refine' (mul_le_mul_of_nonneg_left (d_two hk htk hγ) _).trans _
  ·
    exact
      mul_nonneg (mul_nonneg (exp_pos _).le (rpow_nonneg_of_nonneg (sub_pos_of_lt hγ₁).le _))
        (exp_pos _).le
  rw [← mul_assoc, mul_right_comm (exp _ : ℝ), ← Real.exp_add, mul_mul_mul_comm, ← Real.exp_add,
    add_assoc, ← add_div, ← rpow_nat_cast _ t, ← rpow_add (sub_pos_of_lt hγ₁), neg_add_self,
    rpow_zero, mul_one, neg_mul, ← sub_eq_add_neg, ← mul_sub, sq, ← mul_sub, sub_sub_cancel,
    mul_one]
  refine' mul_le_of_le_one_left (Nat.cast_nonneg _) _
  rw [exp_le_one_iff]
  rw [neg_add_le_iff_le_add, add_zero]
  refine' div_le_one_of_le _ (by positivity)
  exact
    mul_le_mul (hγ₁.le.trans (by norm_num1)) (Nat.cast_le.2 htk) (Nat.cast_nonneg _) (by norm_num1)

theorem nine_five_density :
    ∃ f : ℕ → ℝ,
      (f =o[atTop] fun i => (i : ℝ)) ∧
        ∀ γ₀ : ℝ,
          0 < γ₀ →
            ∀ᶠ l : ℕ in atTop,
              ∀ k : ℕ,
                ∀ γ η : ℝ,
                  γ₀ ≤ γ →
                    0 ≤ η →
                      1 / 2 ≤ 1 - γ - η →
                        ∀ n : ℕ,
                          ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                            (¬∃ (m : Finset (Fin n)) (c : Fin 2),
                                  χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                              ∀ ini : BookConfig χ,
                                1 - γ - η ≤ ini.p →
                                  γ ≤ 1 / 2 →
                                    γ < 1 →
                                      l ≤ k →
                                        1 / 2 ≤ ini.p →
                                          exp (f k) *
                                                (1 - γ - η) ^
                                                  (γ * (redSteps γ k l ini).card / (1 - γ)) *
                                              (1 - γ - η) ^ (redSteps γ k l ini).card ≤
                                            ini.p ^
                                              ((redSteps γ k l ini).card +
                                                (densitySteps γ k l ini).card) :=
  by
  have hp₀ : 0 < (1 / 2 : ℝ) := by norm_num1
  have hμ₁ : (1 / 2 : ℝ) < 1 := by norm_num1
  refine' ⟨fun k => -log 2 * (7 / (1 - 1 / 2) * k ^ (15 / 16 : ℝ)), _, _⟩
  · refine' is_o.const_mul_left _ _
    refine' is_o.const_mul_left _ _
    suffices (fun k : ℝ => k ^ (15 / 16 : ℝ)) =o[at_top] id by
      exact is_o.comp_tendsto this tendsto_nat_cast_atTop_atTop
    simpa using is_o_rpow_rpow (by norm_num1 : 15 / 16 < (1 : ℝ))
  intro γ₀ hγ₀
  filter_upwards [eight_five γ₀ (1 / 2) (1 / 2) hγ₀ hμ₁ hp₀, top_adjuster (eventually_gt_at_top 0),
    beta_le_μ γ₀ _ _ hγ₀ hμ₁ hp₀] with l h₈₅ hk₀ hβμ k γ η hγl hη hγη n χ hχ ini hini hγu hγ₁ hlk
    hp₀'
  specialize h₈₅ k hlk γ hγl hγu n χ hχ ini hp₀'
  specialize hβμ k hlk γ hγl hγu n χ ini hp₀'
  have hst :
    ((density_steps γ k l ini).card : ℝ) ≤
      γ / (1 - γ) * (red_steps γ k l ini).card + 7 / (1 - 1 / 2) * k ^ (15 / 16 : ℝ) :=
    by
    refine' h₈₅.trans (add_le_add_right (mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)) _)
    exact div_le_div (hγ₀.le.trans hγl) hβμ (sub_pos_of_lt hγ₁) (sub_le_sub_left hβμ _)
  have hp₀'' : 0 < ini.p := hp₀.trans_le hp₀'
  rw [← log_inv, ← rpow_def_of_pos, add_comm, ← one_div, pow_add]
  swap
  · norm_num1
  refine'
    mul_le_mul _ (pow_le_pow_of_le_left (hp₀.le.trans hγη) hini _) (pow_nonneg (hp₀.le.trans hγη) _)
      (pow_nonneg col_density_nonneg _)
  rw [← rpow_nat_cast, mul_comm]
  refine' (rpow_le_rpow_of_exponent_ge hp₀'' col_density_le_one hst).trans' _
  rw [div_mul_eq_mul_div γ, rpow_add hp₀'']
  refine'
    mul_le_mul (rpow_le_rpow (hp₀.le.trans hγη) hini _) (rpow_le_rpow hp₀.le hp₀' (by positivity))
      (by positivity) (rpow_nonneg_of_nonneg hp₀''.le _)
  exact div_nonneg (mul_nonneg (hγ₀.le.trans hγl) (Nat.cast_nonneg _)) (sub_pos_of_lt hγ₁).le

theorem nine_five :
    ∃ f : ℕ → ℝ,
      (f =o[atTop] fun i => (i : ℝ)) ∧
        ∀ γ₀ : ℝ,
          0 < γ₀ →
            ∀ᶠ l : ℕ in atTop,
              ∀ k : ℕ,
                l ≤ k →
                  ∀ γ δ η : ℝ,
                    γ = l / (k + l) →
                      γ₀ ≤ γ →
                        0 ≤ δ →
                          δ ≤ γ / 20 →
                            0 ≤ η →
                              1 / 2 ≤ 1 - γ - η →
                                ∀ n : ℕ,
                                  ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                                    (¬∃ (m : Finset (Fin n)) (c : Fin 2),
                                          χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                                      ∀ ini : BookConfig χ,
                                        1 - γ - η ≤ ini.p →
                                          ⌊(n / 2 : ℝ)⌋₊ ≤ ini.y.card →
                                            exp (-δ * k) * (k + l).choose l ≤ n →
                                              Real.exp (-δ * k + f k) *
                                                        (1 - γ - η) ^
                                                          (γ * (redSteps γ k l ini).card /
                                                            (1 - γ)) *
                                                      ((1 - γ - η) / (1 - γ)) ^
                                                        (redSteps γ k l ini).card *
                                                    exp
                                                      (γ * (redSteps γ k l ini).card ^ 2 /
                                                        (2 * k)) *
                                                  (k - (redSteps γ k l ini).card + l).choose l ≤
                                                (endState γ k l ini).y.card :=
  by
  have hp₀ : 0 < (1 / 2 : ℝ) := by norm_num1
  have hμ₁ : (1 / 2 : ℝ) < 1 := by norm_num1
  obtain ⟨f₁, hf₁, hf₁'⟩ := six_one _ hp₀
  obtain ⟨f₂, hf₂, hf₂'⟩ := nine_five_density
  refine' ⟨fun k => log 2 * (f₁ k + -2) + -1 + f₂ k, _, _⟩
  · refine' is_o.add _ hf₂
    refine' is_o.add (is_o.const_mul_left (is_o.add hf₁ _) _) _
    · exact (is_o_const_id_at_top _).comp_tendsto tendsto_nat_cast_atTop_atTop
    · exact (is_o_const_id_at_top _).comp_tendsto tendsto_nat_cast_atTop_atTop
  clear hf₁ hf₂
  intro γ₀ hγ₀
  filter_upwards [eight_five γ₀ (1 / 2) (1 / 2) hγ₀ hμ₁ hp₀, hf₁' γ₀ _ hγ₀ hμ₁, hf₂' γ₀ hγ₀,
    nine_three_lower_n γ₀ hγ₀, top_adjuster (eventually_gt_at_top 0), beta_le_μ γ₀ _ _ hγ₀ hμ₁ hp₀,
    beta_pos γ₀ _ _ hγ₀ hμ₁ hp₀] with l h₈₅ h₆₁ hf₂ hn'' hk₀ hβμ hβ₀ k hlk γ δ η hγ hγl hδ hδu hη
    hγη n χ hχ ini hini hn' hn
  clear hf₁' hf₂'
  have hγu : γ ≤ 1 / 2 := by linarith only [hγη, hη]
  have hγ₁ : γ < 1 := hγu.trans_lt hμ₁
  have hl₀ : 0 < l := hk₀ l le_rfl
  have hp₀' : 1 / 2 ≤ ini.p := hγη.trans hini
  specialize h₈₅ k hlk γ hγl hγu n χ hχ ini hp₀'
  specialize h₆₁ k hlk γ hγl hγu n χ hχ ini hp₀'
  specialize hn'' k γ hγ hγl hγ₁ hlk δ hδu n hn
  specialize hβμ k hlk γ hγl hγu n χ ini hp₀'
  specialize hβ₀ k hlk γ hγl hγu n χ ini hp₀'
  specialize hf₂ k γ η hγl hη hγη n χ hχ ini hini hγu hγ₁ hlk hp₀'
  have htk : (red_steps γ k l ini).card ≤ k := four_four_red _ hχ _
  have : 2 ^ (-2 : ℝ) * (n : ℝ) ≤ ini.Y.card :=
    by
    refine' (Nat.cast_le.2 hn').trans' ((ge_floor _).trans_eq' _)
    · rw [one_le_div (zero_lt_two' ℝ)]
      rw [← @Nat.cast_le ℝ, Nat.cast_two] at hn''
      exact hn''
    rw [div_div, div_eq_mul_inv, mul_comm, ← sq, rpow_neg zero_lt_two.le, rpow_two]
  replace this := (mul_le_mul_of_nonneg_left hn (by positivity)).trans this
  rw [← mul_assoc] at this
  have h₉₆ := nine_six l k (red_steps γ k l ini).card γ (hk₀ k hlk) htk hγ
  replace this := (mul_le_mul_of_nonneg_left h₉₆ (by positivity)).trans this
  clear h₉₆
  have hp₀'' : 0 < ini.p := hp₀.trans_le hp₀'
  refine' h₆₁.trans' ((mul_le_mul_of_nonneg_left this (by positivity)).trans' _)
  clear h₆₁ this
  rw [tsub_add_eq_add_tsub htk, ← mul_assoc, ← mul_assoc, ← mul_assoc,
    rpow_neg (sub_pos_of_lt hγ₁).le (red_steps γ k l ini).card, div_pow, ← mul_assoc, rpow_nat_cast,
    div_eq_mul_inv (_ ^ _), ← mul_assoc]
  refine' mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  refine' mul_le_mul_of_nonneg_right _ (exp_pos _).le
  refine'
    mul_le_mul_of_nonneg_right _ (inv_nonneg_of_nonneg (pow_nonneg (sub_nonneg_of_le hγ₁.le) _))
  rw [mul_mul_mul_comm, ← rpow_add two_pos, ← mul_assoc, mul_assoc _ (Real.exp _), ← Real.exp_add,
    mul_right_comm _ (ini.p ^ _), rpow_def_of_pos two_pos, ← Real.exp_add]
  refine' (mul_le_mul_of_nonneg_left hf₂ (exp_pos _).le).trans' _
  rw [← mul_assoc, ← mul_assoc, ← Real.exp_add]
  rw [← add_assoc, add_left_comm (-δ * k)]

section

variable {V : Type*}

open Fintype

section

/-- The density of a simple graph. -/
def density [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet] : ℚ :=
  G.edgeFinset.card / (card V).choose 2

theorem density_congr [Fintype V] (G₁ G₂ : SimpleGraph V) [Fintype G₁.edgeSet]
    [Fintype G₂.edgeSet] (h : G₁ = G₂) : G₁.density = G₂.density :=
  by
  rw [density, density, edge_finset_card, edge_finset_card]
  congr 2
  refine' card_congr' _
  rw [h]

theorem edgeFinset_eq_filter [Fintype (Sym2 V)] (G : SimpleGraph V) [Fintype G.edgeSet]
    [DecidableRel G.Adj] : G.edgeFinset = univ.filterₓ (· ∈ Sym2.fromRel G.symm) :=
  by
  rw [← Finset.coe_inj, coe_edge_finset, coe_filter, coe_univ, Set.sep_univ]
  rfl

theorem univ_image_quotient_mk' {α : Type*} (s : Finset α) [DecidableEq α] :
    s.offDiag.image Quotient.mk' = s.Sym2.filterₓ fun a => ¬a.IsDiag :=
  (Sym2.filter_image_quotient_mk''_not_isDiag _).symm

theorem edgeFinset_eq_filter_filter [DecidableEq V] [Fintype (Sym2 V)] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] :
    G.edgeFinset = (univ.filterₓ fun a : Sym2 V => ¬a.IsDiag).filterₓ (· ∈ Sym2.fromRel G.symm) :=
  by
  rw [edge_finset_eq_filter, filter_filter]
  refine' filter_congr _
  rw [Sym2.forall]
  intro x y h
  simp only [Sym2.isDiag_iff_proj_eq, iff_and_self, Sym2.fromRel_prop]
  intro h
  exact h.ne

theorem edgeFinset_eq_filter' [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] :
    G.edgeFinset = (univ.offDiag.image Quotient.mk').filterₓ (· ∈ Sym2.fromRel G.symm) := by
  rw [edge_finset_eq_filter_filter, ← sym2_univ, ← univ_image_quotient_mk]

theorem sum_sym2 {α β : Type*} [DecidableEq α] [AddCommMonoid β] {s : Finset α} {f : Sym2 α → β} :
    2 • ∑ x in s.offDiag.image Quotient.mk', f x = ∑ x in s.offDiag, f (Quotient.mk' x) :=
  by
  rw [smul_sum, sum_image']
  rintro ⟨x, y⟩ hxy
  rw [mem_off_diag] at hxy
  obtain ⟨hx : x ∈ s, hy : y ∈ s, hxy : x ≠ y⟩ := hxy
  have hxy' : y ≠ x := hxy.symm
  have : (s.off_diag.filter fun z => ⟦z⟧ = ⟦(x, y)⟧) = ({(x, y), (y, x)} : Finset _) :=
    by
    ext ⟨x₁, y₁⟩
    rw [mem_filter, mem_insert, mem_singleton, Sym2.eq_iff, Prod.mk.inj_iff, Prod.mk.inj_iff,
      and_iff_right_iff_imp]
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> rw [mem_off_diag] <;> exact ⟨‹_›, ‹_›, ‹_›⟩
  rw [this, sum_pair, Sym2.eq_swap, two_smul]
  simpa using hxy

theorem sum_offDiag {α β : Type*} [DecidableEq α] [AddCommMonoid β] {s : Finset α}
    {f : α × α → β} : ∑ x in s.offDiag, f x = ∑ x in s, ∑ y in s.eraseₓ x, f (x, y) :=
  by
  rw [sum_sigma']
  refine' sum_bij (fun x _ => ⟨x.1, x.2⟩) _ _ _ _
  · rintro ⟨x, y⟩ h
    rw [mem_off_diag] at h
    rw [mem_sigma, mem_erase, Ne.def]
    exact ⟨h.1, Ne.symm h.2.2, h.2.1⟩
  · rintro ⟨x, y⟩ h
    rfl
  · rintro ⟨a₁, a₂⟩ ⟨a₃, a₄⟩ _ _ ⟨⟩
    rfl
  rintro ⟨a, b⟩ h
  simp only [mem_sigma, mem_erase] at h
  refine' ⟨(a, b), _⟩
  simp [h.1, h.2.2, Ne.symm h.2.1]

theorem density_eq_average [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] :
    G.density =
      (card V * (card V - 1))⁻¹ * ∑ x : V, ∑ y in univ.eraseₓ x, if G.Adj x y then 1 else 0 :=
  by
  rw [SimpleGraph.density, edge_finset_eq_filter', ← sum_boole, Nat.cast_choose_two,
    div_div_eq_mul_div, mul_comm, ← Nat.cast_two, ← nsmul_eq_mul, sum_sym2, div_eq_mul_inv,
    mul_comm, sum_off_diag]
  rfl

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x y) -/
theorem density_eq_average' [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]
    [DecidableRel G.Adj] :
    G.density = (card V * (card V - 1))⁻¹ * ∑ (x : V) (y : V), if G.Adj x y then 1 else 0 := by
  classical
  rw [density_eq_average]
  congr 2 with x : 1
  simp

theorem density_eq_average_neighbors [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]
    [DecidableRel G.Adj] :
    G.density = (card V * (card V - 1))⁻¹ * ∑ x : V, (G.neighborFinset x).card :=
  by
  rw [density_eq_average']
  congr 2 with x : 1
  simp [neighborFinset_eq_filter]

theorem density_compl [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]
    [Fintype Gᶜ.edgeSet] (h : 2 ≤ card V) : Gᶜ.density = 1 - G.density :=
  by
  rw [SimpleGraph.density, card_compl_edge_finset_eq, Nat.cast_sub edge_finset_card_le, ←
    one_sub_div, SimpleGraph.density]
  rw [Nat.cast_ne_zero, ← pos_iff_ne_zero]
  exact Nat.choose_pos h

theorem sum_ite_fintype {α β : Type*} [Fintype α] [DecidableEq α] [AddCommMonoid β] (s : Finset α)
    (f : α → β) : ∑ x in s, f x = ∑ x, ite (x ∈ s) (f x) 0 := by simp only [sum_ite_mem, univ_inter]

theorem sum_powersetCard_erase {α β : Type*} [Fintype α] [DecidableEq α] [AddCommMonoid β] {n : ℕ}
    {s : Finset α} (f : Finset α → α → β) :
    ∑ U in powersetCard n s, ∑ y in Uᶜ, f U y = ∑ y, ∑ U in powersetCard n (s.eraseₓ y), f U y :=
  by
  simp_rw [sum_ite_fintype (_ᶜ : Finset α), @sum_comm _ α]
  refine' sum_congr rfl fun y hy => _
  rw [← sum_filter]
  refine' sum_congr _ fun _ _ => rfl
  ext U
  simp [mem_powerset_len, subset_erase]
  tauto

theorem powersetCard_filter_mem {α : Type*} [DecidableEq α] {n : ℕ} {s : Finset α} {x : α}
    (hx : x ∈ s) :
    ((powersetCard (n + 1) s).filterₓ fun U => x ∈ U) =
      (powersetCard n (s.eraseₓ x)).image (insert x) :=
  by
  rw [← insert_erase hx, powerset_len_succ_insert, insert_erase hx, filter_union,
    filter_false_of_mem, filter_true_of_mem, empty_union]
  · simp
  · simp (config := { contextual := true }) [mem_powerset_len, subset_erase]
  · simp

theorem sum_powersetCard_insert {α β : Type*} [DecidableEq α] [AddCommMonoid β] {n : ℕ}
    {s : Finset α} (f : Finset α → α → β) :
    ∑ U in powersetCard (n + 1) s, ∑ x in U, f U x =
      ∑ x in s, ∑ U in powersetCard n (s.eraseₓ x), f (insert x U) x :=
  by
  have :
    ∑ x in s, ∑ U in powerset_len n (s.erase x), f (insert x U) x =
      ∑ x in s, ∑ U in (powerset_len (n + 1) s).filterₓ fun U => x ∈ U, f U x :=
    by
    refine' sum_congr rfl fun x hx => _
    rw [powerset_len_filter_mem hx, sum_image _]
    simp only [mem_powerset_len, subset_erase, and_imp]
    intro y hy hy' hy'' z hz hz' hz'' h
    rw [← erase_insert hy', h, erase_insert hz']
  rw [this]
  simp only [sum_filter, @sum_comm _ _ α]
  refine' sum_congr rfl fun U hU => _
  simp only [mem_powerset_len] at hU
  simp only [sum_ite_mem]
  rw [(inter_eq_right_iff_subset _ _).2 hU.1]

theorem erase_eq_filter {α : Type*} [DecidableEq α] {s : Finset α} (a : α) :
    s.eraseₓ a = s.filterₓ (· ≠ a) :=
  by
  rw [filter_not, Finset.filter_eq']
  split_ifs
  · rw [sdiff_singleton_eq_erase]
  · rw [erase_eq_of_not_mem h, sdiff_empty]

theorem sum_pair_subset {α β : Type*} [Fintype α] [DecidableEq α] [AddCommMonoid β] {n : ℕ}
    {s : Finset α} (f : Finset α → α → α → β) :
    ∑ U in powersetCard (n + 1) s, ∑ x in U, ∑ y in Uᶜ, f U x y =
      ∑ x in s, ∑ y in univ.eraseₓ x, ∑ U in powersetCard n (s \ {x, y}), f (insert x U) x y :=
  by
  simp_rw [@sum_comm _ α α _ _ (_ᶜ)]
  rw [sum_powerset_len_erase]
  simp only [sum_powerset_len_insert]
  rw [sum_sigma' univ, sum_sigma' s]
  refine' sum_bij (fun x hx => ⟨x.2, x.1⟩) _ _ _ _
  · simp (config := { contextual := true }) [eq_comm]
  · rintro ⟨x, y⟩ hx
    refine' sum_congr _ fun y hy => rfl
    dsimp
    rw [sdiff_insert, sdiff_singleton_eq_erase]
  · rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
    simp (config := { contextual := true })
  · rintro ⟨x, y⟩
    simp only [mem_sigma, mem_erase, mem_univ, and_true_iff, Sigma.exists, true_and_iff, heq_iff_eq,
      and_imp, exists_prop, and_assoc']
    intro hx hxy
    exact ⟨y, x, hxy.symm, hx, rfl, rfl⟩

theorem choose_helper {n k : ℕ} (h : k + 1 < n) :
    (n.choose (k + 1) : ℚ)⁻¹ * ((n - 2).choose k * (1 / ((k + 1) * (n - (k + 1))))) =
      (n * (n - 1))⁻¹ :=
  by
  have : k + 2 ≤ n := h
  have : 2 ≤ n := h.trans_le' (by simp)
  obtain ⟨n, rfl⟩ := le_iff_exists_add'.1 this
  rw [add_tsub_cancel_right]
  clear this h
  simp only [add_le_add_iff_right] at this
  rw [one_div, mul_left_comm, ← mul_inv, ← one_div, ← one_div, mul_one_div, mul_left_comm, ←
    Nat.cast_add_one, ← Nat.cast_sub, ← Nat.cast_mul, ← Nat.choose_mul_succ_eq, ← Nat.cast_mul, ←
    mul_assoc, mul_comm (k + 1), ← Nat.succ_mul_choose_eq, mul_comm (n + 1), mul_assoc,
    Nat.cast_mul, ← div_div, div_self, mul_comm, Nat.cast_mul, Nat.cast_add n 2, Nat.cast_two,
    add_sub_assoc, Nat.cast_add_one]
  · norm_num1; rfl
  · rw [Nat.cast_ne_zero, ← pos_iff_ne_zero]
    exact Nat.choose_pos this
  · linarith

variable [Fintype V]

theorem density_eq_average_partition [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (n : ℕ) (hn₀ : 0 < n) (hn : n < card V) :
    G.density = ((card V).choose n)⁻¹ * ∑ U in powersetCard n univ, G.edgeDensity U (Uᶜ) :=
  by
  cases n
  · simpa using hn₀
  simp only [SimpleGraph.edgeDensity_def, SimpleGraph.interedges_def, ← sum_boole, sum_div,
    sum_product, density_eq_average, mul_sum]
  rw [sum_pair_subset]
  refine' sum_congr rfl _
  intro x hx
  refine' sum_congr rfl _
  intro y hy
  split_ifs
  swap
  · simp
  simp only [← mul_sum]
  have :
    ∑ U : Finset V in powerset_len n (univ \ {x, y}),
        (1 : ℚ) / ((insert x U).card * insert x Uᶜ.card) =
      ∑ U : Finset V in powerset_len n (univ \ {x, y}), 1 / ((n + 1) * (card V - (n + 1))) :=
    by
    refine' sum_congr rfl fun U hU => _
    simp only [mem_powerset_len, subset_sdiff, disjoint_insert_right, disjoint_singleton_right,
      subset_univ, true_and_iff, and_assoc'] at hU
    rw [card_compl, card_insert_of_not_mem hU.1, hU.2.2, Nat.cast_sub hn.le, Nat.cast_add_one]
  rw [this, sum_const, card_powerset_len, card_sdiff (subset_univ _), card_univ,
    card_doubleton h.ne, mul_one, nsmul_eq_mul]
  rw [choose_helper hn]

theorem exists_density_edgeDensity [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (n : ℕ) (hn₀ : 0 < n) (hn : n < card V) :
    ∃ U : Finset V, U.card = n ∧ G.density ≤ G.edgeDensity U (Uᶜ) :=
  by
  suffices ∃ U ∈ powerset_len n (univ : Finset V), G.density ≤ G.edge_density U (Uᶜ) by
    simpa [mem_powerset_len]
  refine' exists_le_of_sum_le _ _
  · rw [← Finset.card_pos, card_powerset_len, card_univ]
    exact Nat.choose_pos hn.le
  rw [sum_const, density_eq_average_partition _ _ hn₀ hn, card_powerset_len, card_univ,
    nsmul_eq_mul, mul_inv_cancel_left₀]
  rw [Nat.cast_ne_zero]
  exact (Nat.choose_pos hn.le).ne'

theorem exists_equibipartition_edgeDensity (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (hn : 2 ≤ card V) :
    ∃ X Y : Finset V,
      Disjoint X Y ∧
        ⌊(card V / 2 : ℝ)⌋₊ ≤ X.card ∧
          ⌊(card V / 2 : ℝ)⌋₊ ≤ Y.card ∧ G.density ≤ G.edgeDensity X Y :=
  by
  classical
  rw [← Nat.cast_two, Nat.floor_div_eq_div]
  have h₁ : 0 < card V / 2 := Nat.div_pos hn two_pos
  have h₂ : card V / 2 < card V := Nat.div_lt_self (pos_of_gt hn) one_lt_two
  obtain ⟨U, hU, hU'⟩ := exists_density_edge_density G (card V / 2) h₁ h₂
  refine' ⟨U, Uᶜ, disjoint_compl_right, hU.ge, _, hU'⟩
  rw [card_compl, hU, le_tsub_iff_left h₂.le, ← two_mul]
  exact Nat.mul_div_le _ _

end

/-- The density of a label in the edge labelling. -/
def TopEdgeLabelling.density [Fintype V] {K : Type*} (χ : TopEdgeLabelling V K) (k : K)
    [Fintype (χ.labelGraph k).edgeSet] : ℝ :=
  density (χ.labelGraph k)

theorem exists_equibipartition_col_density {n : ℕ} (χ : TopEdgeLabelling (Fin n) (Fin 2))
    (hn : 2 ≤ n) :
    ∃ ini : BookConfig χ,
      χ.density 0 ≤ ini.p ∧ ⌊(n / 2 : ℝ)⌋₊ ≤ ini.X.card ∧ ⌊(n / 2 : ℝ)⌋₊ ≤ ini.y.card :=
  by
  obtain ⟨X, Y, hd, hX, hY, p⟩ :=
    exists_equibipartition_edge_density (χ.labelGraph 0) (by simpa using hn)
  rw [Fintype.card_fin] at hX hY
  refine' ⟨⟨X, Y, ∅, ∅, hd, _, _, _, _, _, _, _, _, _⟩, Rat.cast_le.2 p, hX, hY⟩
  all_goals simp

theorem density_zero_one [Fintype V] (χ : TopEdgeLabelling V (Fin 2))
    [Fintype (χ.labelGraph 0).edgeSet] [Fintype (χ.labelGraph 1).edgeSet]
    (h : 2 ≤ card V) : χ.density 0 = 1 - χ.density 1 := by
  classical
  rw [TopEdgeLabelling.density, TopEdgeLabelling.density, ← Rat.cast_one, ← Rat.cast_sub,
    Rat.cast_inj, ← density_compl (χ.labelGraph 1) h]
  refine' density_congr _ _ _
  rw [← to_EdgeLabelling_labelGraph_compl, labelGraph_to_EdgeLabelling]

end

theorem nine_two_monotone {γ η : ℝ} (γ' δ' : ℝ) (hγu : γ ≤ γ') (hηγ : δ' ≤ 1 - γ' - η) (hδ : 0 < δ')
    (hγ1 : γ' < 1) (hδ' : δ' ≤ 1) : δ' ^ (1 / (1 - γ')) ≤ (1 - γ - η) ^ (1 / (1 - γ)) :=
  by
  have : δ' ≤ 1 - γ - η := hηγ.trans (by linarith only [hγu])
  refine' (rpow_le_rpow hδ.le this _).trans' _
  · exact div_nonneg (by norm_num1) (by linarith only [hγu, hγ1])
  refine' rpow_le_rpow_of_exponent_ge hδ hδ' _
  exact div_le_div_of_le_left zero_le_one (sub_pos_of_lt hγ1) (by linarith only [hγu])

theorem nine_two_numeric_aux {γ η : ℝ} (hγu : γ ≤ 1 / 10) (hηγ : η ≤ γ / 15) :
    (134 / 150) ^ (10 / 9 : ℝ) ≤ (1 - γ - η) ^ (1 / (1 - γ)) :=
  by
  refine' (nine_two_monotone (1 / 10) (67 / 75) hγu _ _ _ _).trans_eq' _
  · linarith only [hηγ, hγu]
  · norm_num1
  · norm_num1
  · norm_num1
  · norm_num

theorem nine_two_numeric {γ η : ℝ} (hγu : γ ≤ 1 / 10) (hηγ : η ≤ γ / 15) :
    exp (-1 / 3 + 1 / 5) ≤ (1 - γ - η) ^ (1 / (1 - γ)) :=
  by
  refine' (nine_two_numeric_aux hγu hηγ).trans' _
  have : (0 : ℝ) < 134 / 150 := by norm_num1
  rw [← le_log_iff_exp_le (rpow_pos_of_pos this _), log_rpow this, ← div_le_iff']
  swap; · positivity
  norm_num1
  rw [neg_le, ← log_inv, inv_div, le_div_iff, mul_comm, ← log_rpow, log_le_iff_le_exp, ←
    exp_one_rpow]
  · refine' (rpow_le_rpow (by norm_num1) exp_one_gt_d9.le (by norm_num1)).trans' _
    norm_num
  · exact rpow_pos_of_pos (by norm_num1) _
  · norm_num1
  · norm_num1

theorem nine_two_part_two {k t : ℕ} {γ η : ℝ} (hγl : 0 ≤ γ) (hγu : γ ≤ 1 / 10) (hηγ : η ≤ γ / 15)
    (ht : (2 / 3 : ℝ) * k ≤ t) (hk : 0 < k)
    (h : exp (-1 / 3 + 1 / 5) ≤ (1 - γ - η) ^ (1 / (1 - γ))) :
    exp (6 * γ * t ^ 2 / (20 * k)) ≤ exp (γ * t ^ 2 / (2 * k)) * (1 - γ - η) ^ (γ * t / (1 - γ)) :=
  by
  have : 0 < 1 - γ - η := by linarith only [hγu, hηγ]
  rw [div_eq_mul_one_div _ (1 - γ), mul_comm _ (1 / (1 - γ)), rpow_mul this.le]
  refine'
    (mul_le_mul_of_nonneg_left (rpow_le_rpow (exp_pos _).le h (by positivity))
          (exp_pos _).le).trans'
      _
  rw [← exp_one_rpow (_ + _), ← rpow_mul (exp_pos _).le, exp_one_rpow, ← Real.exp_add, exp_le_exp,
    sq, mul_mul_mul_comm, ← div_mul_eq_mul_div, ← mul_assoc γ, mul_div_assoc (γ * t),
    mul_comm (γ * t), ← add_mul, div_add']
  swap; · positivity
  refine' mul_le_mul_of_nonneg_right _ (by positivity)
  rw [div_le_iff, div_mul_eq_mul_div, mul_div_assoc, mul_div_mul_right]
  · linarith
  · positivity
  · positivity

-- lemma nine_two_part_two {k t : ℕ} {γ η : ℝ} (hγl : 0 ≤ γ) (hγu : γ ≤ 1 / 10) (hηγ : η ≤ γ / 15)
--   (ht : (2 / 3 : ℝ) * k ≤ t) (hk : 0 < k)
--   (h : exp (- 1 / 3 + 1 / 5) ≤ (1 - γ - η) ^ (1 / (1 - γ))) :
--   exp ((k : ℝ) * (γ * (2 / 15))) ≤ exp (γ * t ^ 2 / (2 * k)) * (1 - γ - η) ^ (γ * t / (1 - γ)) :=
-- begin
--   have : 0 < 1 - γ - η := by linarith only [hγu, hηγ],
--   rw [div_eq_mul_one_div _ (1 - γ), mul_comm _ (1 / (1 - γ)), rpow_mul this.le],
--   refine (mul_le_mul_of_nonneg_left (rpow_le_rpow (exp_pos _).le h (by positivity))
--     (exp_pos _).le).trans' _,
--   rw [←exp_one_rpow (_ + _), ←rpow_mul (exp_pos _).le, exp_one_rpow, ←real.exp_add, exp_le_exp,
--     sq, ←mul_assoc γ, mul_div_assoc, ←mul_comm (γ * t), ←mul_add],
--   have : (k : ℝ) * (γ * (2 / 15)) ≤ γ * t * (1 / 5),
--   { rw [mul_left_comm, mul_assoc],
--     refine mul_le_mul_of_nonneg_left _ hγl,
--     linarith only [ht] },
--   refine this.trans (mul_le_mul_of_nonneg_left _ (by positivity)),
--   rw [div_add', le_div_iff],
--   { linarith only [ht] },
--   { positivity },
--   { positivity },
-- end
theorem nine_two_part_three {η γ : ℝ} (hγl : 0 ≤ η) (hγu : γ ≤ 1 / 10) (hηγ : η ≤ γ / 15) :
    exp (-3 * η / 2) ≤ (1 - γ - η) / (1 - γ) :=
  by
  rw [← one_sub_div, ← div_mul_eq_mul_div]
  swap; · linarith
  have h₂ : -1 / 3 ≤ -3 / 2 * η := by linarith
  refine' (general_convex_thing' (by linarith) h₂ (by norm_num)).trans _
  have : 1 + -10 / 9 * η ≤ 1 - η / (1 - γ) :=
    by
    rw [neg_div, neg_mul, ← sub_eq_add_neg, sub_le_sub_iff_left, div_eq_mul_one_div, mul_comm]
    refine' mul_le_mul_of_nonneg_right _ hγl
    rw [div_le_iff] <;> linarith
  refine' this.trans' _
  rw [← mul_assoc, ← div_mul_eq_mul_div, add_le_add_iff_left]
  refine' mul_le_mul_of_nonneg_right _ hγl
  suffices exp (-1 / 3) ≤ 61 / 81
    by
    rw [mul_div_assoc, ← le_div_iff, sub_le_iff_le_add]
    · exact this.trans_eq (by norm_num1)
    · norm_num1
  refine' le_of_pow_le_pow 3 (by norm_num1) (by norm_num1) _
  rw [← exp_nat_mul, Nat.cast_bit1, Nat.cast_one, mul_div_cancel', ← inv_div, inv_pow, Real.exp_neg]
  · refine' inv_le_inv_of_le (by norm_num1) (exp_one_gt_d9.le.trans' (by norm_num1))
  · norm_num1

theorem nine_two_part_four {k t : ℕ} {η γ : ℝ} (hγl : 0 ≤ η) (hγu : γ ≤ 1 / 10) (hηγ : η ≤ γ / 15)
    (ht : (2 / 3 : ℝ) * k ≤ t) (hk : 0 < k) :
    exp (-3 * γ * t ^ 2 / (20 * k)) ≤ ((1 - γ - η) / (1 - γ)) ^ t :=
  by
  refine' (pow_le_pow_of_le_left (exp_pos _).le (nine_two_part_three hγl hγu hηγ) _).trans' _
  rw [← exp_nat_mul, exp_le_exp, neg_mul, neg_mul, neg_div, neg_mul, neg_div, mul_neg,
    neg_le_neg_iff, mul_div_assoc, mul_left_comm, ← mul_assoc, sq, mul_mul_mul_comm, mul_div_assoc]
  refine' mul_le_mul_of_nonneg_left _ (by positivity)
  refine' (div_le_div_of_le (by positivity) hηγ).trans _
  rw [div_div, div_eq_mul_one_div, mul_div_assoc]
  refine' mul_le_mul_of_nonneg_left _ (by linarith)
  rw [le_div_iff, ← mul_assoc]
  · exact ht.trans' (mul_le_mul_of_nonneg_right (by norm_num1) (Nat.cast_nonneg _))
  · positivity

theorem nine_two_part_five {k t : ℕ} {η γ γ₀ δ fk : ℝ} (hη₀ : 0 ≤ η) (hγu : γ ≤ 1 / 10)
    (hηγ : η ≤ γ / 15) (hγ₀' : 0 < γ) (h₂ : 0 ≤ 1 - γ - η) (ht : (2 / 3 : ℝ) * k ≤ t) (hk : 0 < k)
    (hδ : δ = γ / 20) (hγ₀ : γ₀ ≤ γ) (hγ₁ : γ < 1) (hfk : -fk ≤ γ₀ / 60 * k) :
    1 ≤
      exp (-δ * k + fk) * (1 - γ - η) ^ (γ * t / (1 - γ)) * ((1 - γ - η) / (1 - γ)) ^ t *
        exp (γ * t ^ 2 / (2 * ↑k)) :=
  by
  rw [mul_right_comm _ ((1 - γ - η) ^ (_ : ℝ)), mul_right_comm, mul_assoc]
  refine'
    (mul_le_mul_of_nonneg_left (nine_two_part_two hγ₀'.le hγu hηγ ht hk (nine_two_numeric hγu hηγ))
          _).trans'
      _
  · exact mul_nonneg (exp_pos _).le (pow_nonneg (div_nonneg h₂ (sub_pos_of_lt hγ₁).le) _)
  rw [mul_right_comm, ← Real.exp_add]
  refine' (mul_le_mul_of_nonneg_left (nine_two_part_four hη₀ hγu hηγ ht hk) (exp_pos _).le).trans' _
  rw [← Real.exp_add, one_le_exp_iff, add_right_comm _ fk, add_right_comm _ fk, neg_mul, neg_mul,
    neg_mul, neg_div, add_assoc (-_), ← sub_eq_add_neg, ← sub_div, ← sub_neg_eq_add _ fk,
    sub_nonneg]
  have : -(((2 / 3) ^ 2)⁻¹ * γ * t ^ 2 / (20 * k)) ≤ -(δ * k) :=
    by
    rw [neg_le_neg_iff, hδ, ← div_div, le_div_iff, mul_assoc, ← sq, ← div_mul_eq_mul_div,
      mul_div_assoc, mul_assoc, mul_left_comm]
    swap
    · rw [Nat.cast_pos]
      exact hk
    refine' mul_le_mul_of_nonneg_left _ (div_nonneg hγ₀'.le (by norm_num1))
    rw [inv_mul_eq_div, le_div_iff', ← mul_pow]
    · exact pow_le_pow_of_le_left (by positivity) ht _
    · positivity
  have hfk' : -fk ≤ γ / 60 * k :=
    hfk.trans (mul_le_mul_of_nonneg_right (by linarith only [hγ₀]) (Nat.cast_nonneg _))
  refine' hfk'.trans ((add_le_add_right this _).trans' _)
  rw [neg_add_eq_sub, ← sub_div, mul_assoc, mul_assoc, mul_assoc, ← sub_mul, ← sub_mul, ← div_div,
    le_div_iff, mul_assoc, ← sq, div_mul_comm, mul_comm, mul_left_comm, mul_div_assoc, ←
    div_mul_eq_mul_div]
  swap
  · positivity
  refine' mul_le_mul_of_nonneg_left _ hγ₀'.le
  rw [← div_le_iff', div_div, div_eq_mul_one_div]
  swap
  · norm_num1
  refine' (pow_le_pow_of_le_left (by positivity) ht _).trans_eq' _
  ring

-- TODO: move
section

variable {V K : Type*} {n : K → ℕ}

theorem ramsey_number_le_finset_aux {s : Finset V} (C : TopEdgeLabelling V K)
    (h :
      ∃ (m : Finset s) (c : K),
        (C.pullback (Function.Embedding.subType* : s ↪ V)).MonochromaticOf m c ∧ n c ≤ m.card) :
    ∃ (m : Finset V) (c : K), m ⊆ s ∧ C.MonochromaticOf m c ∧ n c ≤ m.card :=
  by
  obtain ⟨m, c, hm, hn⟩ := h
  refine' ⟨_, c, _, hm.map, hn.trans_eq (card_map _).symm⟩
  simp only [subset_iff, Finset.mem_map, Function.Embedding.coe_subtype, exists_prop,
    Subtype.exists, Subtype.coe_mk, exists_and_right, exists_eq_right, forall_exists_index]
  intro x hx _
  exact hx

-- there should be a version of this for is_ramsey_valid and it should be useful *for* the proof
-- that ramsey numbers exist
theorem ramseyNumber_le_finset [DecidableEq K] [Fintype K] {s : Finset V}
    (h : ramseyNumber n ≤ s.card) (C : TopEdgeLabelling V K) :
    ∃ (m : Finset V) (c : K), m ⊆ s ∧ C.MonochromaticOf m c ∧ n c ≤ m.card :=
  by
  have : ramsey_number n ≤ Fintype.card s := by rwa [Fintype.card_coe]
  rw [ramsey_number_le_iff, is_ramsey_valid] at this
  exact ramsey_number_le_finset_aux _ (this _)

theorem ramseyNumber_le_choose' {i j : ℕ} : ramseyNumber ![i, j] ≤ (i + j).choose i :=
  ((ramseyNumber.mono_two (Nat.le_succ _) (Nat.le_succ _)).trans
        (ramseyNumber_le_choose (i + 1) (j + 1))).trans
    (by simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero, Nat.add_succ, Nat.succ_add_sub_one])

end

theorem nine_two (γ₀ : ℝ) (hγ₀ : 0 < γ₀) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k : ℕ,
        ∀ γ δ η : ℝ,
          γ = l / (k + l) →
            γ₀ ≤ γ →
              γ ≤ 1 / 10 →
                δ = γ / 20 →
                  0 ≤ η →
                    η ≤ γ / 15 →
                      ∀ n : ℕ,
                        ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                          1 - γ - η ≤ χ.density 0 →
                            exp (-δ * k) * (k + l).choose l ≤ n →
                              ∃ (m : Finset (Fin n)) (c : Fin 2),
                                χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card :=
  by
  obtain ⟨f, hf, hf'⟩ := nine_five
  filter_upwards [nine_three_lower_n γ₀ hγ₀, nine_three γ₀ hγ₀, hf' γ₀ hγ₀,
    top_adjuster (eventually_gt_at_top 0),
    top_adjuster (hf.bound (div_pos hγ₀ (by norm_num1) : 0 < γ₀ / 60))] with l hn₂ h₉₃ h₉₅ hk₀ hfk k
    γ δ η hγ hγl hγu hδ hη₀ hηγ n χ hχd hn
  clear hf'
  have hγ₁ : γ < 1 := hγu.trans_lt (by norm_num1)
  have hl₀ : 0 < l := hk₀ l le_rfl
  have hlk := le_of_gamma_le_half hγ hl₀ (hγu.trans (by norm_num1))
  have hγ₀' : 0 < γ := hγ₀.trans_le hγl
  have hδ' : δ = min (1 / 200) (γ / 20) :=
    by
    rw [hδ, min_eq_right]
    linarith only [hγu]
  have hδ₀ : 0 ≤ δ := by
    rw [hδ]
    exact div_nonneg hγ₀'.le (by norm_num1)
  by_contra hχ
  have hp₀ : 1 / 2 ≤ 1 - γ - η := by linarith only [hγu, hηγ]
  specialize hn₂ k γ hγ hγl hγ₁ hlk δ hδ.le n hn
  obtain ⟨ini, hini, hXc, hYc⟩ := exists_equibipartition_col_density χ hn₂
  replace hini := hχd.trans hini
  have hini4 : 1 / 4 ≤ ini.p := hini.trans' (hp₀.trans' (by norm_num1))
  specialize h₉₃ k hlk γ hγ hγl (hγu.trans (by norm_num1)) δ hδ' n χ hχ ini hini4 hXc hn
  specialize h₉₅ k hlk γ δ η hγ hγl hδ₀ hδ.le hη₀ hp₀ n χ hχ ini hini hYc hn
  specialize hfk k hlk
  clear hδ'
  rw [norm_eq_abs, abs_le', norm_coe_nat] at hfk
  have :
    1 ≤
      exp (-δ * k + f k) * (1 - γ - η) ^ (γ * ↑(red_steps γ k l ini).card / (1 - γ)) *
          ((1 - γ - η) / (1 - γ)) ^ (red_steps γ k l ini).card *
        exp (γ * ↑(red_steps γ k l ini).card ^ 2 / (2 * ↑k)) :=
    nine_two_part_five hη₀ hγu hηγ hγ₀' (hp₀.trans' (by norm_num1)) h₉₃ (hk₀ k hlk) hδ hγl hγ₁ hfk.2
  replace h₉₅ := h₉₅.trans' (mul_le_mul_of_nonneg_right this (Nat.cast_nonneg _))
  rw [one_mul, Nat.cast_le, ← Nat.choose_symm_add] at h₉₅
  have := ramsey_number_le_finset (ramsey_number_le_choose'.trans h₉₅) χ
  simp only [Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, tsub_le_iff_left,
    Matrix.head_cons] at this hχ
  obtain ⟨m, ⟨hm₀, hm₁, hm₂⟩ | ⟨hm₀, hm₁, hm₂⟩⟩ := this
  swap
  · exact hχ ⟨m, Or.inr ⟨hm₁, hm₂⟩⟩
  refine' hχ ⟨(end_state γ k l ini).A ∪ m, Or.inl ⟨_, hm₂.trans _⟩⟩
  · rw [coe_union, TopEdgeLabelling.MonochromaticOf_union]
    refine' ⟨(end_state γ k l ini).red_a, hm₁, _⟩
    exact (end_state γ k l ini).red_XYA.symm.subset_right (hm₀.trans (subset_union_right _ _))
  rwa [card_union_eq, add_le_add_iff_right]
  · exact t_le_A_card γ k l ini
  exact (end_state γ k l ini).hYA.symm.mono_right hm₀

/-- A finite set viewed as a finset is equivalent to itself. -/
def Equiv.toFinset {α : Type*} {s : Set α} [Fintype s] : s.toFinset ≃ s :=
  ⟨fun x => ⟨x, by simpa using x.2⟩, fun x => ⟨x, by simp⟩, fun x => Subtype.ext rfl, fun x =>
    Subtype.ext rfl⟩

theorem Finset.card_congr_of_equiv {α β : Type*} {s : Finset α} {t : Finset β} (e : s ≃ t) :
    s.card = t.card :=
  by
  refine'
    Finset.card_congr (fun x hx => e ⟨x, hx⟩) (fun x hx => (e _).2) (fun x y hx hy h => _)
      fun x hx => ⟨e.symm ⟨x, hx⟩, (e.symm _).2, _⟩
  · rw [← Subtype.ext_iff, Equiv.apply_eq_iff_eq, Subtype.ext_iff] at h
    exact h
  rw [Subtype.coe_eta, Equiv.apply_symm_apply, Subtype.coe_mk]

theorem density_graph_iso {V V' : Type*} [Fintype V] [Fintype V'] [DecidableEq V] [DecidableEq V']
    {G : SimpleGraph V} {G' : SimpleGraph V'} [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (e : G ≃g G') : G.density = G'.density :=
  by
  rw [SimpleGraph.density, e.card_eq_of_iso, SimpleGraph.edgeFinset, SimpleGraph.density,
    SimpleGraph.edgeFinset, finset.card_congr_of_equiv]
  exact equiv.to_finset.trans (e.map_edgeSet.trans equiv.to_finset.symm)

/-- Pulling back a colouring along an equivalence induces a graph isomorphism -/
def labelGraphIso {V V' K : Type*} {χ : TopEdgeLabelling V K} (k : K) (f : V' ≃ V) :
    (χ.pullback f.toEmbedding).labelGraph k ≃g χ.labelGraph k
    where
  toEquiv := f
  map_rel_iff' := by
    intro x y
    simp only [Ne.def, EmbeddingLike.apply_eq_iff_eq, Equiv.coe_toEmbedding,
      TopEdgeLabelling.labelGraph_adj, TopEdgeLabelling.pullback_get]

theorem nine_two_variant (γ₀ : ℝ) (hγ₀ : 0 < γ₀) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k : ℕ,
        ∀ γ δ η : ℝ,
          γ = l / (k + l) →
            γ₀ ≤ γ →
              γ ≤ 1 / 10 →
                δ = γ / 20 →
                  0 ≤ η →
                    η ≤ γ / 15 →
                      ∀ V : Type*,
                        DecidableEq V →
                          Fintype V →
                            ∀ χ : TopEdgeLabelling V (Fin 2),
                              1 - γ - η ≤ χ.density 0 →
                                exp (-δ * k) * (k + l).choose l ≤ Fintype.card V →
                                  ∃ (m : Finset V) (c : Fin 2),
                                    χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card :=
  by
  filter_upwards [nine_two γ₀ hγ₀] with l hl k γ δ η hγ hγl hγu hδ hη hηγ V _ _ χ hχ hn
  skip
  obtain ⟨e⟩ := Fintype.truncEquivFin V
  let χ' : TopEdgeLabelling (Fin (Fintype.card V)) (Fin 2) := χ.pullback e.symm.to_embedding
  have : 1 - γ - η ≤ χ'.density 0 := by
    refine' hχ.trans_eq _
    rw [TopEdgeLabelling.density, TopEdgeLabelling.density, Rat.cast_inj]
    refine' density_graph_iso _
    exact (labelGraph_iso _ _).symm
  obtain ⟨m, c, hm, hmc⟩ := hl k γ δ η hγ hγl hγu hδ hη hηγ (Fintype.card V) χ' this hn
  refine' ⟨m.map e.symm.to_embedding, c, hm.map, hmc.trans _⟩
  rw [card_map]

theorem nine_one_part_one {m : ℝ} (hm : 1 < m) : (⌈(m / exp 1 : ℝ)⌉₊ : ℝ) < m :=
  by
  have : 1 / 2 < m / 2 := div_lt_div_of_lt two_pos hm
  refine' ((ceil_lt_two_mul this).trans_le' _).trans_eq _
  · refine' Nat.cast_le.2 (Nat.ceil_mono _)
    exact div_le_div_of_le_left (by linarith) two_pos (exp_one_gt_d9.le.trans' (by norm_num1))
  exact mul_div_cancel' _ two_pos.ne'

theorem gamma'_le_gamma_iff {k l m : ℕ} (h : m ≤ l) (h' : 0 < k) :
    (l - m : ℝ) / (k + l - m) < (l / (k + l)) ^ 2 ↔ (l * (k + l) : ℝ) / (k + 2 * l) < m :=
  by
  have :
    (l : ℝ) * l * (k + l - m) - (l - m) * ((k + l) * (k + l)) =
      k * (m * (k + 2 * l) - l * (k + l)) :=
    by ring_nf
  rw [div_pow, div_lt_iff, div_lt_iff, div_mul_eq_mul_div, lt_div_iff, ← sub_pos, sq, sq, this,
    mul_pos_iff, or_iff_left, and_iff_right, sub_pos]
  · rwa [Nat.cast_pos]
  · simp only [not_and', not_lt, Nat.cast_nonneg, imp_true_iff]
  · positivity
  · positivity
  rw [add_sub_assoc, ← Nat.cast_sub h]
  positivity

theorem gamma_hMul_k_le_m_of {k l m : ℕ} (h : m ≤ l) (h' : 0 < k)
    (hg : (l - m : ℝ) / (k + l - m) < (l / (k + l)) ^ 2) : (l / (k + l) : ℝ) * k ≤ m :=
  by
  rw [gamma'_le_gamma_iff h h'] at hg
  refine' hg.le.trans' _
  rw [div_mul_eq_mul_div, div_le_div_iff, ← sub_nonneg]
  · ring_nf
    positivity
  · positivity
  · positivity

/-- Part of the right hand side of (50) -/
noncomputable def uLowerBoundRatio (ξ : ℝ) (k l m : ℕ) : ℝ :=
  (1 + ξ) ^ m * ∏ i in range m, (l - i) / (k + l - i)

theorem uLowerBoundRatio_eq {ξ : ℝ} (k l m : ℕ) :
    uLowerBoundRatio ξ k l m = ∏ i in range m, (1 + ξ) * ((l - i) / (k + l - i)) :=
  by
  rw [U_lower_bound_ratio, prod_mul_distrib]
  simp

theorem uLowerBoundRatio_of_l_lt_m {ξ : ℝ} {k l m : ℕ} (h : l < m) : uLowerBoundRatio ξ k l m = 0 :=
  by
  rw [← mem_range] at h
  rw [U_lower_bound_ratio, prod_eq_zero h, MulZeroClass.mul_zero]
  rw [sub_self, zero_div]

theorem uLowerBoundRatio_nonneg {ξ : ℝ} {k l m : ℕ} (hξ : 0 ≤ ξ) : 0 ≤ uLowerBoundRatio ξ k l m :=
  by
  cases lt_or_le l m
  · rw [U_lower_bound_ratio_of_l_lt_m h]
  rw [U_lower_bound_ratio_eq]
  refine' prod_nonneg fun i hi => _
  have : (0 : ℝ) ≤ l - i := by
    rw [sub_nonneg, Nat.cast_le]
    exact h.trans' (mem_range.1 hi).le
  rw [mem_range] at hi
  refine' mul_nonneg (by linarith only [hξ]) (div_nonneg this _)
  rw [add_sub_assoc]
  exact add_nonneg (Nat.cast_nonneg _) this

theorem uLowerBoundRatio_pos {ξ : ℝ} {k l m : ℕ} (hξ : 0 ≤ ξ) (h : m ≤ l) :
    0 < uLowerBoundRatio ξ k l m := by
  rw [U_lower_bound_ratio_eq]
  refine' prod_pos _
  intro i hi
  rw [mem_range] at hi
  rw [add_sub_assoc]
  have : (0 : ℝ) < l - i := by
    rw [sub_pos, Nat.cast_lt]
    exact hi.trans_le h
  positivity

theorem U_lower_bound_decreasing {ξ : ℝ} (k l : ℕ) (hξ : 0 ≤ ξ) (hξ' : ξ ≤ 1) (hlk : l ≤ k)
    (hk : 0 < k) : Antitone (uLowerBoundRatio ξ k l) :=
  by
  refine' antitone_nat_of_succ_le _
  intro m
  cases le_or_lt l m
  · rw [U_lower_bound_ratio_of_l_lt_m]
    · exact U_lower_bound_ratio_nonneg hξ
    rwa [Nat.lt_add_one_iff]
  rw [U_lower_bound_ratio_eq, prod_range_succ, ← U_lower_bound_ratio_eq]
  refine' mul_le_of_le_one_right _ _
  · exact U_lower_bound_ratio_nonneg hξ
  rw [mul_div_assoc', add_sub_assoc, ← Nat.cast_sub h.le, div_le_one, add_comm, add_one_mul,
    add_le_add_iff_right]
  · refine' (mul_le_of_le_one_left (Nat.cast_nonneg _) hξ').trans _
    rw [Nat.cast_le]
    exact (Nat.sub_le _ _).trans hlk
  positivity

theorem xi_numeric : exp (1 / 20) < 1 + 1 / 16 :=
  by
  refine' lt_of_pow_lt_pow 20 (by norm_num1) _
  rw [← exp_nat_mul]
  refine' (exp_one_lt_d9.trans_eq' (by norm_num)).trans_le _
  norm_num

theorem uLowerBoundRatio_lower_bound_aux_aux {k l m n : ℕ} {γ δ : ℝ} (hml : m ≤ l) (hk₀ : 0 < k)
    (hγ : γ = l / (k + l)) (hδ : δ = γ / 20) (hg : (l - m : ℝ) / (k + l - m) < (l / (k + l)) ^ 2)
    (hn : exp (-δ * k) * (k + l).choose l ≤ n) :
    ((k + l - m).choose k : ℝ) ≤ n * uLowerBoundRatio (1 / 16) k l m :=
  by
  have : ((l + k - m).choose _ : ℝ) / _ = _ := choose_ratio hml
  rw [U_lower_bound_ratio, add_comm (k : ℝ), ← this]
  refine' (mul_le_mul_of_nonneg_right hn _).trans' _
  · positivity
  rw [mul_div_assoc', mul_assoc, ← Nat.choose_symm_add, add_comm l, mul_div_cancel',
    add_tsub_assoc_of_le hml, Nat.choose_symm_add, ← mul_assoc]
  swap
  · rw [Nat.cast_ne_zero, ← pos_iff_ne_zero]
    exact Nat.choose_pos (by simp)
  refine' le_mul_of_one_le_left (Nat.cast_nonneg _) _
  rw [neg_mul, Real.exp_neg, inv_mul_eq_div, one_le_div (exp_pos _), hδ, div_mul_eq_mul_div, hγ]
  refine' (pow_le_pow_of_le_left (exp_pos _).le xi_numeric.le m).trans' _
  rw [← exp_nat_mul, mul_one_div, exp_le_exp]
  exact div_le_div_of_le (by norm_num1) (gamma_mul_k_le_m_of hml hk₀ hg)

theorem uLowerBoundRatio_lower_bound_aux {k l m n : ℕ} {γ δ : ℝ} (hml : m < l) (hk₀ : 0 < k)
    (hγ : γ = l / (k + l)) (hδ : δ = γ / 20) (hg : (l - m : ℝ) / (k + l - m) < (l / (k + l)) ^ 2)
    (hn : exp (-δ * k) * (k + l).choose l ≤ n) : (k : ℝ) ≤ n * uLowerBoundRatio (1 / 16) k l m :=
  by
  refine' (U_lower_bound_ratio_lower_bound_aux_aux hml.le hk₀ hγ hδ hg hn).trans' _
  rw [Nat.cast_le, add_tsub_assoc_of_le hml.le]
  have : 1 ≤ l - m := by
    rw [Nat.succ_le_iff]
    exact Nat.sub_pos_of_lt hml
  refine' (Nat.choose_le_choose k (add_le_add_left this k)).trans' _
  rw [Nat.choose_symm_add, Nat.choose_one_right]
  simp

theorem uLowerBoundRatio_lower_bound' {k l m n : ℕ} {γ δ : ℝ} (hml : m < l) (hk₀ : 0 < k)
    (hlk : l ≤ k) (hγ : γ = l / (k + l)) (hδ : δ = γ / 20)
    (hn : exp (-δ * k) * (k + l).choose l ≤ n) (h : (k : ℝ) < (l - 2) * l) :
    (k : ℝ) ≤ n * uLowerBoundRatio (1 / 16) k l m :=
  by
  cases' lt_or_le ((l - m : ℝ) / (k + l - m)) ((l / (k + l)) ^ 2) with h' h'
  · exact U_lower_bound_ratio_lower_bound_aux hml hk₀ hγ hδ h' hn
  let mst := ⌊(l * (k + l) : ℝ) / (k + 2 * l)⌋₊ + 1
  have hm : m < mst :=
    by
    rw [← not_lt, gamma'_le_gamma_iff hml.le hk₀, not_lt] at h'
    rw [← @Nat.cast_lt ℝ]
    refine' h'.trans_lt _
    rw [Nat.cast_add_one]
    exact Nat.lt_floor_add_one _
  rw [← sub_pos] at h
  have : mst < l := by
    rw [← @Nat.cast_lt ℝ, Nat.cast_add_one, ← lt_sub_iff_add_lt]
    refine' (Nat.floor_le (by positivity)).trans_lt _
    rw [div_lt_iff, ← sub_pos]
    · ring_nf; exact h
    · positivity
  refine'
    (U_lower_bound_ratio_lower_bound_aux this hk₀ hγ hδ _ hn).trans
      (mul_le_mul_of_nonneg_left
        (U_lower_bound_decreasing k l (by norm_num1) (by norm_num1) hlk hk₀ hm.le)
        (Nat.cast_nonneg _))
  rw [gamma'_le_gamma_iff this.le hk₀, Nat.cast_add_one]
  exact Nat.lt_floor_add_one _

theorem small_k {k l : ℕ} {γ γ₀ : ℝ} (hγ₀ : 0 < γ₀) (hγl : γ₀ ≤ γ) (hγ : γ = l / (k + l))
    (hk₀ : 0 < k) : (k : ℝ) ≤ l * (γ₀⁻¹ - 1) :=
  by
  subst γ
  rwa [le_div_iff, ← le_div_iff' hγ₀, ← le_sub_iff_add_le, div_eq_mul_inv, ← mul_sub_one] at hγl
  positivity

/-- Cliques which are useful for section 9 and 10 -/
def IsGoodClique {n : ℕ} (ξ : ℝ) (k l : ℕ) (χ : TopEdgeLabelling (Fin n) (Fin 2))
    (x : Finset (Fin n)) : Prop :=
  χ.MonochromaticOf x 1 ∧ (n : ℝ) * uLowerBoundRatio ξ k l x.card ≤ (commonBlues χ x).card

theorem empty_is_good {n k l : ℕ} {ξ : ℝ} {χ : TopEdgeLabelling (Fin n) (Fin 2)} :
    IsGoodClique ξ k l χ ∅ := by
  constructor
  · simp
  rw [U_lower_bound_ratio_eq, card_empty, prod_range_zero, mul_one, Nat.cast_le, common_blues]
  simp

theorem good_clique_bound {n k l ξ} {χ : TopEdgeLabelling (Fin n) (Fin 2)} {x : Finset (Fin n)}
    (hχ : ¬∃ (m : Finset (Fin n)) (c : Fin 2), χ.MonochromaticOf (↑m) c ∧ ![k, l] c ≤ m.card)
    (hx : IsGoodClique ξ k l χ x) : x.card < l :=
  by
  by_contra'
  exact hχ ⟨x, 1, hx.1, by simpa using this⟩

theorem commonBlues_insert {V : Type*} [Fintype V] [DecidableEq V] {x : Finset V} {i : V}
    {χ : TopEdgeLabelling V (Fin 2)} :
    commonBlues χ (insert i x) = (blue_neighbors χ) i ∩ commonBlues χ x :=
  by
  ext v
  simp [common_blues]

theorem maximally_good_clique_aux {V : Type*} [DecidableEq V] [Fintype V]
    {χ : TopEdgeLabelling V (Fin 2)} {U : Finset V} :
    (χ.pullback (Function.Embedding.subtype (· ∈ U))).density 1 =
      (U.card * (U.card - 1))⁻¹ * ∑ v in U, ((blue_neighbors χ) v ∩ U).card :=
  by
  rw [TopEdgeLabelling.density, density_eq_average_neighbors, Fintype.subtype_card,
    filter_mem_eq_inter, univ_inter, Rat.cast_mul, ← Nat.cast_sum, ← Nat.cast_sum, Rat.cast_inv,
    Rat.cast_mul, Rat.cast_sub, Rat.cast_one, Rat.cast_coe_nat, Rat.cast_coe_nat]
  congr 2
  refine' sum_bij (fun x _ => x) (fun x _ => x.2) _ (fun _ _ _ _ => Subtype.ext) _
  swap
  · intro x hx
    refine' ⟨⟨x, hx⟩, mem_univ _, rfl⟩
  rintro ⟨x, hx⟩ -
  refine' card_congr (fun x _ => x) _ (fun _ _ _ _ => Subtype.ext) _
  · simp only [Subtype.forall, mem_neighborFinset, TopEdgeLabelling.labelGraph_adj,
      TopEdgeLabelling.pullback_get, mem_inter, mem_col_neighbors, forall_exists_index, Ne.def,
      Function.Embedding.coe_subtype, Subtype.coe_mk, coe_mem, and_true_iff]
    intro y hy h hxy
    exact ⟨h, hxy⟩
  · intro y
    simp only [mem_neighborFinset, TopEdgeLabelling.labelGraph_adj, mem_col_neighbors,
      mem_inter, Subtype.exists, Subtype.coe_mk, and_imp, exists_imp, Ne.def,
      Function.Embedding.coe_subtype, exists_prop, exists_eq_right, exists_and_right,
      TopEdgeLabelling.pullback_get]
    intro h h' hy
    exact ⟨hy, h, h'⟩

theorem big_U {U : ℕ} (hU : 256 ≤ U) : (U : ℝ) / (U - 1) * (1 + 1 / 16) ≤ 1 + 1 / 15 :=
  by
  have : (256 : ℝ) ≤ U := (Nat.cast_le.2 hU).trans_eq' (by norm_num1)
  rw [div_mul_eq_mul_div, div_le_iff] <;> linarith

-- here
theorem maximally_good_clique {n k l : ℕ} {ξ ξ' : ℝ} {χ : TopEdgeLabelling (Fin n) (Fin 2)}
    (hξ : 0 ≤ ξ)
    (hχ : ¬∃ (m : Finset (Fin n)) (c : Fin 2), χ.MonochromaticOf (↑m) c ∧ ![k, l] c ≤ m.card)
    {x : Finset (Fin n)}
    (hU : ((commonBlues χ x).card : ℝ) / ((commonBlues χ x).card - 1) * (1 + ξ) ≤ 1 + ξ')
    (hU' : 2 ≤ (commonBlues χ x).card) (hx : IsGoodClique ξ k l χ x)
    (h : ∀ i : Fin n, i ∉ x → IsGoodClique ξ k l χ (insert i x) → False) :
    1 - (1 + ξ') * ((l - x.card : ℝ) / (k + l - x.card)) ≤
      (χ.pullback (Function.Embedding.subType* : commonBlues χ x ↪ Fin n)).density 0 :=
  by
  classical
  have hml := good_clique_bound hχ hx
  rw [is_good_clique] at hx
  have :
    ∀ i ∈ common_blues χ x,
      i ∉ x ∧
        ¬(n : ℝ) * U_lower_bound_ratio ξ k l (insert i x).card ≤
            (common_blues χ (insert i x)).card :=
    by
    intro i hi
    rw [common_blues, mem_filter] at hi
    have : i ∉ x := by
      intro h'
      exact not_mem_col_neighbors (hi.2 i h')
    refine' ⟨this, fun hi' => h i this ⟨_, hi'⟩⟩
    rw [coe_insert, TopEdgeLabelling.MonochromaticOf_insert]
    swap
    · exact this
    refine' ⟨hx.1, _⟩
    intro y hy
    have := hi.2 y hy
    rw [mem_col_neighbors'] at this
    obtain ⟨_, z⟩ := this
    exact z
  have hz :
    ∀ i ∈ common_blues χ x,
      (((blue_neighbors χ) i ∩ common_blues χ x).card : ℝ) <
        (common_blues χ x).card * ((1 + ξ) * ((l - x.card) / (k + l - x.card))) :=
    by
    intro i hi
    obtain ⟨hi', hi''⟩ := this i hi
    rw [card_insert_of_not_mem hi', not_le, common_blues_insert, U_lower_bound_ratio_eq,
      prod_range_succ, ← U_lower_bound_ratio_eq, ← mul_assoc, add_sub_assoc] at hi''
    have : (0 : ℝ) < (1 + ξ) * ((l - x.card) / (k + (l - x.card))) :=
      by
      have : (0 : ℝ) < l - x.card := by rwa [sub_pos, Nat.cast_lt]
      positivity
    replace hi'' := hi''.trans_le (mul_le_mul_of_nonneg_right hx.2 this.le)
    rwa [add_sub_assoc'] at hi''
  rw [density_zero_one, maximally_good_clique_aux, sub_le_sub_iff_left]
  swap
  · rw [Fintype.subtype_card, filter_mem_eq_inter, univ_inter]
    exact hU'
  refine' (mul_le_mul_of_nonneg_left (sum_le_sum fun i hi => (hz i hi).le) _).trans _
  · rw [inv_nonneg]
    refine' mul_nonneg (Nat.cast_nonneg _) _
    rw [sub_nonneg, Nat.one_le_cast]
    exact hU'.trans' (by norm_num1)
  rw [sum_const, nsmul_eq_mul, inv_mul_eq_div, mul_div_mul_left, ← div_mul_eq_mul_div, ← mul_assoc]
  swap
  · rw [Nat.cast_ne_zero]
    linarith only [hU']
  refine' mul_le_mul_of_nonneg_right _ _
  swap
  · rw [add_sub_assoc, ← Nat.cast_sub hml.le]
    positivity
  exact hU

theorem nine_one_end {k l n : ℕ} {ξ : ℝ} {χ : TopEdgeLabelling (Fin n) (Fin 2)} {x : Finset (Fin n)}
    (hχ : ¬∃ (m : Finset (Fin n)) (c : Fin 2), χ.MonochromaticOf (↑m) c ∧ ![k, l] c ≤ m.card)
    (hx : IsGoodClique ξ k l χ x)
    (h :
      ∃ (m : Finset (Fin n)) (c : Fin 2),
        m ⊆ commonBlues χ x ∧ χ.MonochromaticOf (↑m) c ∧ ![k, l - x.card] c ≤ m.card) :
    False :=
  by
  simp only [Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    tsub_le_iff_right] at h
  obtain ⟨m, hm | ⟨hm, hm', hm''⟩⟩ := h
  · exact hχ ⟨m, 0, hm.2⟩
  have : Disjoint m x := by
    refine' Disjoint.mono_left hm _
    simp only [disjoint_right, common_blues, mem_filter, mem_col_neighbors, mem_univ, true_and_iff,
      Classical.not_forall, not_exists]
    intro i hi
    exact ⟨i, hi, fun q => (q rfl).elim⟩
  refine' hχ ⟨m ∪ x, 1, _, by simpa [this] using hm''⟩
  rw [coe_union, TopEdgeLabelling.MonochromaticOf_union]
  exact ⟨hm', hx.1, monochromatic_between_common_blues.symm.subset_left hm⟩

theorem nine_one_part_two {k l n : ℕ} {γ δ : ℝ} {χ : TopEdgeLabelling (Fin n) (Fin 2)}
    {x : Finset (Fin n)}
    (hχ : ¬∃ (m : Finset (Fin n)) (c : Fin 2), χ.MonochromaticOf (↑m) c ∧ ![k, l] c ≤ m.card)
    (hml : x.card < l) (hl₀ : 0 < l) (hlk : l ≤ k) (hγ : γ = l / (k + l)) (hδ : δ = γ / 20)
    (hm : exp (-δ * k) * (k + l).choose l ≤ n) (hx : IsGoodClique (1 / 16) k l χ x)
    (hγ' : (l - x.card : ℝ) / (k + l - x.card) < (l / (k + l)) ^ 2) : False :=
  by
  have :=
    Nat.cast_le.1
      ((U_lower_bound_ratio_lower_bound_aux_aux hml.le (hl₀.trans_le hlk) hγ hδ hγ' hm).trans hx.2)
  rw [add_tsub_assoc_of_le hml.le] at this
  have := ramsey_number_le_finset (ramsey_number_le_choose'.trans this) χ
  exact nine_one_end hχ hx this

theorem nine_one_part_three {k l m : ℕ} {γ γ' δ : ℝ} (hml : m < l) (hk₀ : 0 < k)
    (hγ : γ = l / (k + l)) (hδ : δ = γ / 20) (hγ' : γ' = (l - m) / (k + l - m))
    (h :
      exp (-δ * k) * (k + l).choose l * uLowerBoundRatio (1 / 16) k l m <
        exp (-(γ' / 20) * k) * ↑((k + (l - m)).choose (l - m))) :
    False := by
  have : ((l + k - m).choose _ : ℝ) / _ = _ := choose_ratio hml.le
  rw [← Nat.cast_add, add_comm l, add_tsub_assoc_of_le hml.le, Nat.choose_symm_add] at this
  rw [← not_le] at h
  refine' h _
  rw [U_lower_bound_ratio, ← Nat.cast_add, ← this, Nat.choose_symm_add, mul_assoc, mul_div_assoc',
    mul_div_cancel', ← mul_assoc]
  swap
  · rw [Nat.cast_ne_zero, ← pos_iff_ne_zero]
    exact Nat.choose_pos (by simp)
  refine' mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  refine'
    (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_left (exp_pos _).le xi_numeric.le _)
          (exp_pos _).le).trans'
      _
  rw [← exp_nat_mul, ← Real.exp_add, exp_le_exp, hδ, neg_mul, neg_mul, neg_add_eq_sub,
    le_sub_iff_add_le, neg_add_eq_sub, mul_one_div, div_mul_eq_mul_div, div_mul_eq_mul_div, ←
    sub_div, hγ, hγ', ← sub_mul]
  refine' div_le_div_of_le (by norm_num1) _
  rw [← le_div_iff]
  swap
  · rw [Nat.cast_pos]; exact hk₀
  refine' (sub_le_sub_left (div_le_div_of_le_left _ _ (sub_le_self _ _)) _).trans _
  · rw [sub_nonneg, Nat.cast_le]; exact hml.le
  · rw [add_sub_assoc, ← Nat.cast_sub hml.le]; positivity
  · exact Nat.cast_nonneg _
  rw [← sub_div, sub_sub_self]
  exact div_le_div_of_le_left (Nat.cast_nonneg _) (by positivity) (by simp)

theorem gamma'_le_gamma {k l m : ℕ} (hk : 0 < k) (h : m ≤ l) :
    (l - m : ℝ) / (k + l - m) ≤ l / (k + l) :=
  by
  rw [div_le_div_iff, ← sub_nonneg]
  · ring_nf
    positivity
  · rw [add_sub_assoc, ← Nat.cast_sub h]; positivity
  · positivity

theorem l_minus_m_big (γ₀ : ℝ) {k l m : ℕ} (hml : m ≤ l) (hl₀ : 0 < l)
    (hkl : (k : ℝ) ≤ l * (γ₀⁻¹ - 1)) (h₁ : 0 < γ₀⁻¹ - 1 + 2) (h₂ : 0 < (γ₀⁻¹ - 1 + 2)⁻¹)
    (hγ' : (m : ℝ) ≤ l * (k + ↑l) / (k + 2 * l)) : ⌈(l : ℝ) * (γ₀⁻¹ - 1 + 2)⁻¹⌉₊ ≤ l - m :=
  by
  rw [Nat.ceil_le, Nat.cast_sub hml, le_sub_comm, ← mul_one_sub]
  refine' hγ'.trans _
  rw [mul_div_assoc]
  refine' mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  rw [div_le_iff, one_sub_mul, le_sub_comm, add_sub_add_left_eq_sub]
  swap
  · positivity
  refine' (mul_le_mul_of_nonneg_left (add_le_add_right hkl _) h₂.le).trans _
  rw [mul_comm (2 : ℝ), ← mul_add, mul_left_comm, inv_mul_cancel h₁.ne']
  linarith

/- ./././Mathport/Syntax/Translate/Basic.lean:641:2: warning: expanding binder collection (i «expr ∉ » x) -/
theorem nine_one_precise (γ₀ : ℝ) (hγ₀ : 0 < γ₀) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k : ℕ,
        ∀ γ δ : ℝ,
          γ = l / (k + l) →
            γ₀ ≤ γ →
              γ ≤ 1 / 10 →
                δ = γ / 20 → (ramseyNumber ![k, l] : ℝ) ≤ exp (-δ * k + 1) * (k + l).choose l :=
  by
  have h₁ : 0 < γ₀⁻¹ - 1 + 2 := by rw [sub_add]; norm_num; positivity
  have h₂ : 0 < (γ₀⁻¹ - 1 + 2)⁻¹ := by positivity
  have q :=
    (tendsto_nat_ceil_at_top.comp (tendsto_id.at_top_mul_const' h₂)).comp
      tendsto_nat_cast_atTop_atTop
  filter_upwards [top_adjuster (eventually_ge_at_top 2), eventually_gt_at_top 0,
    eventually_ge_at_top 256, eventually_gt_at_top ⌊γ₀⁻¹ - 1 + 2⌋₊,
    q.eventually (top_adjuster (nine_two_variant (γ₀ ^ 2) (pow_pos hγ₀ _)))] with l hk₂ hl₀ hk₂₅₆
    hlγ₀ hk₉₂ k γ δ hγ hγl hγu hδ
  let n := ⌈(ramsey_number ![k, l] / exp 1 : ℝ)⌉₊
  have hlk := le_of_gamma_le_half hγ hl₀ (hγu.trans (by norm_num1))
  have hnr : n < ramsey_number ![k, l] :=
    by
    rw [← @Nat.cast_lt ℝ]
    refine' nine_one_part_one _
    simp only [Nat.one_lt_cast]
    refine' ramsey_number_ge_min _ _
    simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    exact ⟨hk₂ _ hlk, hk₂ _ le_rfl⟩
  rw [← not_le, ramsey_number_le_iff_fin, is_ramsey_valid, Classical.not_forall] at hnr
  obtain ⟨χ : TopEdgeLabelling (Fin n) (Fin 2), hχ⟩ := hnr
  suffices (n : ℝ) ≤ exp (-δ * k) * (k + l).choose l
    by
    rw [add_comm, Real.exp_add, mul_assoc, ← div_le_iff' (exp_pos _)]
    exact this.trans' (Nat.le_ceil _)
  by_contra' hm
  classical
  have : (univ.filter (is_good_clique (1 / 16) k l χ)).Nonempty :=
    ⟨∅, by simp only [mem_filter, empty_is_good, mem_univ, true_and_iff]⟩
  obtain ⟨x, hx, hxy⟩ := exists_maximal _ this
  simp only [mem_filter, mem_univ, true_and_iff] at hx hxy
  have hml := good_clique_bound hχ hx
  let U := common_blues χ x
  have hkl := small_k hγ₀ hγl hγ (hl₀.trans_le hlk)
  have : 256 ≤ U.card := by
    refine' (hk₂₅₆.trans hlk).trans _
    rw [← @Nat.cast_le ℝ]
    refine' hx.2.trans' _
    refine' U_lower_bound_ratio_lower_bound' hml (hl₀.trans_le hlk) hlk hγ hδ hm.le _
    rw [mul_comm]
    refine' hkl.trans_lt _
    refine' mul_lt_mul_of_pos_left _ (Nat.cast_pos.2 hl₀)
    rwa [lt_sub_iff_add_lt, ← Nat.floor_lt' hl₀.ne']
  let m := x.card
  let γ' : ℝ := (l - m) / (k + l - m)
  cases' lt_or_le γ' ((l / (k + l)) ^ 2) with hγ' hγ'
  · exact nine_one_part_two hχ hml hl₀ hlk hγ hδ hm.le hx hγ'
  have hγ'γ : γ' ≤ γ := (gamma'_le_gamma (hl₀.trans_le hlk) hml.le).trans_eq hγ.symm
  have hlm : ⌈(l : ℝ) * (γ₀⁻¹ - 1 + 2)⁻¹⌉₊ ≤ l - m :=
    by
    rw [← not_lt, gamma'_le_gamma_iff hml.le (hl₀.trans_le hlk), not_lt] at hγ'
    exact l_minus_m_big _ hml.le hl₀ hkl h₁ h₂ hγ'
  have hγ'_eq : γ' = ↑(l - m) / (↑k + ↑(l - m)) := by rw [Nat.cast_sub hml.le, add_sub_assoc']
  have hγ'₀ : 0 ≤ γ' := by
    rw [hγ'_eq]
    positivity
  have hxy' : ∀ (i) (_ : i ∉ x), is_good_clique (1 / 16) k l χ (insert i x) → False :=
    by
    intro i hi hi'
    exact hxy (insert i x) hi' (ssubset_insert hi)
  have := maximally_good_clique (by norm_num1) hχ (big_U this) (this.trans' (by norm_num1)) hx hxy'
  rw [one_add_mul, mul_comm (1 / 15 : ℝ), mul_one_div, ← sub_sub] at this
  specialize
    hk₉₂ (l - m) hlm k γ' (γ' / 20) (γ' / 15) hγ'_eq
      (hγ'.trans' (pow_le_pow_of_le_left hγ₀.le (hγl.trans_eq hγ) _)) (hγ'γ.trans hγu) rfl
      (div_nonneg hγ'₀ (by norm_num1)) le_rfl _ _ _ _ this
  replace hk₉₂ := fun z => nine_one_end hχ hx (ramsey_number_le_finset_aux _ (hk₉₂ z))
  rw [imp_false, not_le, Fintype.subtype_card, filter_mem_eq_inter, univ_inter] at hk₉₂
  replace hk₉₂ := hx.2.trans hk₉₂.le
  replace hk₉₂ :=
    (mul_lt_mul_of_pos_right hm (U_lower_bound_ratio_pos (by norm_num1) hml.le)).trans_le hk₉₂
  exact nine_one_part_three hml (hl₀.trans_le hlk) hγ hδ rfl hk₉₂

theorem nine_one_o_filter (γ₀ : ℝ) (hγ₀ : 0 < γ₀) :
    ∃ f : ℕ → ℝ,
      (f =o[atTop] fun i => (i : ℝ)) ∧
        ∀ᶠ l : ℕ in atTop,
          ∀ k : ℕ,
            ∀ γ δ : ℝ,
              γ = l / (k + l) →
                γ₀ ≤ γ →
                  γ ≤ 1 / 10 →
                    δ = γ / 20 →
                      (ramseyNumber ![k, l] : ℝ) ≤ exp (-δ * k + f k) * (k + l).choose l :=
  by
  refine' ⟨fun i => 1, _, nine_one_precise _ hγ₀⟩
  exact is_o.comp_tendsto (is_o_const_id_at_top _) tendsto_nat_cast_atTop_atTop

theorem nine_one_nine :
    ∀ᶠ l in atTop, ∀ k, k = 9 * l → (ramseyNumber ![k, l] : ℝ) ≤ exp (-l / 25) * (k + l).choose l :=
  by
  filter_upwards [nine_one_precise (1 / 10) (by norm_num1), eventually_ge_at_top 200] with l hl hl'
    k hk
  subst hk
  refine' (hl (9 * l) (1 / 10) (1 / 10 / 20) _ le_rfl le_rfl rfl).trans _
  · rw [Nat.cast_mul, ← add_one_mul, mul_comm, ← div_div, div_self]
    · norm_num1
    · positivity
  refine' mul_le_mul_of_nonneg_right (exp_le_exp.2 _) (Nat.cast_nonneg _)
  have : (200 : ℝ) ≤ l := by exact_mod_cast hl'
  rw [Nat.cast_mul]
  norm_num1
  linarith

end SimpleGraph

