/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Section10
import Prereq.Mathlib.InformationTheory.BinaryEntropy
import Prereq.Mathlib.Analysis.Calculus.MeanValue
import Prereq.Mathlib.Analysis.SpecialFunctions.Log.Base

#align_import section11

/-!
# Section 11
-/


namespace SimpleGraph

open scoped BigOperators ExponentialRamsey Nat Real

open Filter Finset Nat Real Asymptotics

theorem large_X (n m : ℕ) (hn'' : 2 ≤ n) (hn' : ⌊(n / 2 : ℝ)⌋₊ ≤ m) : (2 : ℝ) ^ (-2 : ℝ) * n ≤ m :=
  by
  refine' (Nat.cast_le.2 hn').trans' ((ge_floor _).trans_eq' _)
  · rw [one_le_div (zero_lt_two' ℝ)]
    exact_mod_cast hn''
  rw [div_div, div_eq_mul_inv, mul_comm]
  norm_num

theorem isLittleO_const_thing {c : ℝ} : (fun _ : ℕ => c) =o[atTop] fun i => (i : ℝ) :=
  IsLittleO.comp_tendsto (isLittleO_const_id_atTop c) tendsto_nat_cast_atTop_atTop

theorem eleven_two_start (μ : ℝ) (hμ₀ : 0 < μ) (hμ₁ : μ < 1) :
    ∃ f : ℕ → ℝ,
      (f =o[atTop] fun i => (i : ℝ)) ∧
        ∀ᶠ k : ℕ in atTop,
          ∀ n : ℕ,
            2 ≤ n →
              ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                (¬∃ (m : Finset (Fin n)) (c : Fin 2), χ.MonochromaticOf m c ∧ ![k, k] c ≤ m.card) →
                  ∀ ini : BookConfig χ,
                    1 / 2 ≤ ini.p →
                      ⌊(n / 2 : ℝ)⌋₊ ≤ ini.X.card →
                        let s := (densitySteps μ k k ini).card
                        let t := (redSteps μ k k ini).card
                        (n : ℝ) ≤ 2 ^ f k * μ⁻¹ ^ k * (1 - μ)⁻¹ ^ t * (μ / beta μ k k ini) ^ s :=
  by
  have hp₀ : (0 : ℝ) < 1 / 2 := by norm_num1
  obtain ⟨f₁, hf₁', hf₁⟩ := end_ramsey_number_pow_is_o
  obtain ⟨f₂, hf₂', hf₂⟩ := seven_one μ hμ₁
  specialize hf₁ μ μ (1 / 2) hμ₀ hμ₁ hp₀
  specialize hf₂ μ (1 / 2) hμ₀ hp₀
  refine' ⟨fun k => 2 + f₁ k + -f₂ k, _, _⟩
  · exact (is_o_const_thing.add hf₁').add hf₂'.neg_left
  clear hf₁' hf₂'
  filter_upwards [hf₁, hf₂, beta_pos μ μ _ hμ₀ hμ₁ hp₀] with k hf₁' hf₂' hβ n hn'' χ hχ ini hini hn'
  clear hf₁ hf₂
  specialize hf₁' k le_rfl μ le_rfl le_rfl n χ hχ ini hini
  specialize hf₂' k le_rfl μ le_rfl le_rfl n χ hχ ini hini
  specialize hβ k le_rfl μ le_rfl le_rfl n χ ini hini
  have hμ₁' : 0 < 1 - μ := sub_pos_of_lt hμ₁
  replace hf₂' := hf₂'.trans hf₁'
  rw [← le_div_iff', div_eq_mul_inv, mul_inv, ← inv_pow, inv_div, mul_inv, mul_inv, ← inv_pow, ←
    inv_pow, ← rpow_neg two_pos.le, mul_assoc, mul_assoc] at hf₂' 
  swap; · positivity
  replace hf₂' := (large_X _ _ hn'' hn').trans hf₂'
  rw [← le_div_iff'] at hf₂' 
  swap; · positivity
  refine' hf₂'.trans_eq _
  rw [div_eq_mul_inv, mul_comm, rpow_neg two_pos.le, inv_inv, ← mul_assoc, ← rpow_add two_pos, ←
    mul_assoc, ← rpow_add two_pos, ← mul_assoc, ← mul_assoc]

theorem logb_pow {b x : ℝ} {k : ℕ} : logb b (x ^ k) = k * logb b x := by
  rw [logb, log_pow, mul_div_assoc, logb]

theorem IsO.max {f g h : ℕ → ℝ} (hf : f =o[atTop] h) (hg : g =o[atTop] h) :
    (fun x => max (f x) (g x)) =o[atTop] h :=
  by
  rw [is_o_iff]
  intro c hc
  filter_upwards [hf.bound hc, hg.bound hc] with n hf' hg'
  rw [norm_eq_abs]
  refine' abs_max_le_max_abs_abs.trans _
  rw [← norm_eq_abs, ← norm_eq_abs, max_le_iff]
  exact ⟨hf', hg'⟩

theorem log_one_add_o (f : ℕ → ℝ) (hf : f =o[atTop] fun _ => (1 : ℝ)) :
    (fun k => log (1 + f k)) =o[atTop] fun _ => (1 : ℝ) :=
  by
  rw [is_o_one_iff] at hf ⊢
  rw [← log_one]
  refine' (continuous_at_log one_ne_zero).Tendsto.comp _
  convert (@tendsto_const_nhds _ _ _ 1 _).add hf using 1
  rw [add_zero]

theorem logb_isBigO_log (b : ℝ) (l) : logb b =O[l] log :=
  by
  rw [is_O_iff]
  refine' ⟨‖(log b)⁻¹‖, _⟩
  filter_upwards with k
  rw [logb, div_eq_mul_inv, norm_mul, mul_comm]

-- logb (1 + o(1)) is o(1)
theorem logb_one_add_o {b : ℝ} (f : ℕ → ℝ) (hf : f =o[atTop] fun _ => (1 : ℝ)) :
    (fun k => logb b (1 + f k)) =o[atTop] fun _ => (1 : ℝ) :=
  by
  refine' (is_O.comp_tendsto (logb_is_O_log _ (nhds 1)) _).trans_isLittleO (log_one_add_o _ hf)
  rw [is_o_one_iff] at hf 
  convert (@tendsto_const_nhds _ _ _ 1 _).add hf using 1
  rw [add_zero]

theorem isLittleO_logb_rpow_atTop {b r : ℝ} (hr : 0 < r) : logb b =o[atTop] fun x => x ^ r :=
  ((isLittleO_log_rpow_atTop hr).const_mul_left (log b)⁻¹).congr_left fun x => inv_mul_eq_div _ _

theorem eleven_two_aux_error_one (μ : ℝ) (hμ₀ : 0 < μ) :
    ∃ f : ℕ → ℝ,
      (f =o[atTop] fun i => (i : ℝ)) ∧
        ∀ k : ℕ,
          ∀ s t : ℕ,
            t ≤ k → (s : ℝ) ≤ k ^ (31 / 32 : ℝ) → (s : ℝ) * logb 2 (μ * (s + t) / s) ≤ f k :=
  by
  refine' ⟨fun k => ‖(k ^ (31 / 32 : ℝ) * (logb 2 μ + 1) + k ^ (31 / 32 : ℝ) * logb 2 k : ℝ)‖, _, _⟩
  · rw [is_o_norm_left]
    suffices
      (fun k : ℝ => k ^ (31 / 32 : ℝ) * (logb 2 μ + 1) + k ^ (31 / 32 : ℝ) * logb 2 k) =o[at_top] id
      by exact this.comp_tendsto tendsto_nat_cast_atTop_atTop
    refine' is_o.add _ _
    · simp_rw [mul_comm]
      refine' is_o.const_mul_left _ _
      refine' (is_o_rpow_rpow (by norm_num1 : (31 / 32 : ℝ) < 1)).congr_right _
      simp
    have : (fun x : ℝ => x ^ (31 / 32 : ℝ)) =O[at_top] fun x : ℝ => x ^ (31 / 32 : ℝ) :=
      is_O_refl _ _
    refine'
      (is_O.mul_is_o this (is_o_logb_rpow_at_top (show (0 : ℝ) < 1 / 32 by norm_num1))).congr'
        eventually_eq.rfl _
    filter_upwards [eventually_gt_at_top (0 : ℝ)] with k hk
    rw [← rpow_add hk]
    norm_num1
    rw [rpow_one, id.def]
  intro k s t ht hs
  rcases s.eq_zero_or_pos with (rfl | hs₀)
  · rw [Nat.cast_zero, MulZeroClass.zero_mul]
    exact norm_nonneg _
  have hsk : s ≤ k := by
    rw [← @Nat.cast_le ℝ]
    refine' hs.trans _
    rcases k.eq_zero_or_pos with (rfl | hk)
    · norm_num
    have : 1 ≤ (k : ℝ) := by
      rw [Nat.one_le_cast]
      exact hk
    exact (rpow_le_rpow_of_exponent_le this (by norm_num1)).trans_eq (rpow_one _)
  have : 0 < k := hs₀.trans_le hsk
  cases le_or_lt (logb 2 (μ * (s + t) / s)) 0
  · exact (norm_nonneg _).trans' (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) h)
  rw [norm_eq_abs, ← mul_add, abs_mul]
  refine' (mul_le_mul_of_nonneg_right (hs.trans (le_abs_self _)) h.le).trans _
  refine' mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  refine' (le_abs_self _).trans' _
  rw [add_assoc, mul_div_assoc, logb_mul hμ₀.ne', add_le_add_iff_left,
    logb_le_iff_le_rpow one_lt_two, add_comm (1 : ℝ), rpow_add_one two_ne_zero,
    rpow_logb two_pos one_lt_two.ne']
  refine' (div_le_self (by positivity) _).trans _
  · rwa [Nat.one_le_cast]
  rotate_left
  · positivity
  · positivity
  · positivity
  rw [mul_two, ← Nat.cast_add, ← Nat.cast_add, Nat.cast_le]
  · exact add_le_add hsk ht

theorem logb_coe_nonneg (b : ℝ) (hb : 1 < b) (k : ℕ) : 0 ≤ logb b k :=
  by
  cases k
  · rw [Nat.cast_zero, logb_zero]
  refine' logb_nonneg hb _
  simp

theorem logb_le_logb_of_le {b x y : ℝ} (hb : 1 ≤ b) (hx : 0 < x) (hxy : x ≤ y) :
    logb b x ≤ logb b y := by
  rcases eq_or_lt_of_le hb with (rfl | hb')
  · rw [logb, logb, log_one, div_zero, div_zero]
  rwa [logb_le_logb hb' hx (hx.trans_le hxy)]

theorem eleven_two_aux_error_one' (μ : ℝ) (hμ₀ : 0 < μ) :
    ∃ f : ℕ → ℝ,
      (f =o[atTop] fun i => (i : ℝ)) ∧
        ∀ k s t : ℕ,
          t ≤ k → (s : ℝ) ≤ k ^ (31 / 32 : ℝ) → |(s : ℝ) * logb 2 (μ * (s + t) / s)| ≤ f k :=
  by
  refine' ⟨fun k => (k : ℝ) ^ (31 / 32 : ℝ) * (|logb 2 μ| + 1 + 2 * logb 2 k), _, _⟩
  · suffices (fun k : ℝ => k ^ (31 / 32 : ℝ) * (|logb 2 μ| + 1 + 2 * logb 2 k)) =o[at_top] id by
      exact this.comp_tendsto tendsto_nat_cast_atTop_atTop
    suffices (fun k : ℝ => |logb 2 μ| + 1 + 2 * logb 2 k) =o[at_top] fun k : ℝ => k ^ (1 / 32 : ℝ)
      by
      refine'
        ((is_O_refl (fun k : ℝ => k ^ (31 / 32 : ℝ)) at_top).mul_isLittleO this).congr'
          eventually_eq.rfl _
      filter_upwards [eventually_gt_at_top (0 : ℝ)] with k hk using by norm_num [← rpow_add hk]
    refine' is_o.add _ _
    · rw [is_o_const_left]
      exact Or.inr (tendsto_norm_at_top_at_top.comp (tendsto_rpow_atTop (by norm_num1)))
    refine' is_o.const_mul_left _ _
    exact is_o_logb_rpow_at_top (by norm_num1)
  intro k s t htk hsk
  rcases s.eq_zero_or_pos with (rfl | hs)
  · rw [Nat.cast_zero, MulZeroClass.zero_mul, abs_zero]
    have := logb_coe_nonneg 2 one_lt_two k
    positivity
  have : s ≤ k := by
    rw [← @Nat.cast_le ℝ]
    refine' hsk.trans _
    rcases k.eq_zero_or_pos with (rfl | hk)
    · norm_num
    have : 1 ≤ (k : ℝ) := by
      rw [Nat.one_le_cast]
      exact hk
    exact (rpow_le_rpow_of_exponent_le this (by norm_num1)).trans_eq (rpow_one _)
  rw [abs_mul, Nat.abs_cast, logb_div, logb_mul hμ₀.ne', add_sub_assoc, add_assoc]
  rotate_left
  · positivity
  · positivity
  · positivity
  refine' mul_le_mul hsk ((abs_add _ _).trans (add_le_add_left _ _)) (abs_nonneg _) (by positivity)
  refine' (abs_sub _ _).trans _
  have : 1 + logb 2 k = logb 2 (2 * k) :=
    by
    rw [logb_mul, add_left_inj, logb, div_self]
    · exact log_ne_zero_of_pos_of_ne_one two_pos one_lt_two.ne'
    · norm_num1
    · have : 0 < k := hs.trans_le this; positivity
  rw [← Nat.cast_add, abs_of_nonneg (logb_coe_nonneg _ one_lt_two _), Nat.cast_add,
    abs_of_nonneg (logb_coe_nonneg _ one_lt_two _), two_mul, ← add_assoc, this, two_mul]
  refine' add_le_add (logb_le_logb_of_le one_lt_two.le _ _) (logb_le_logb_of_le one_lt_two.le _ _)
  any_goals positivity
  any_goals norm_cast
  · exact add_le_add ‹_› htk
  · exact ‹s ≤ k›

theorem eleven_two_aux_error_one_other (μ : ℝ) (hμ₀ : 0 < μ) :
    ∃ f : ℕ → ℝ,
      (f =o[atTop] fun i => (i : ℝ)) ∧
        ∀ k s : ℕ,
          ∀ β : ℝ,
            0 < β →
              (1 : ℝ) / k ^ 2 ≤ β → (s : ℝ) ≤ k ^ (31 / 32 : ℝ) → (s : ℝ) * logb 2 (μ / β) ≤ f k :=
  by
  refine'
    ⟨fun k => ‖logb 2 μ * (k : ℝ) ^ (31 / 32 : ℝ) + 2 * ((k : ℝ) ^ (31 / 32 : ℝ) * logb 2 k)‖, _, _⟩
  · rw [is_o_norm_left]
    suffices
      (fun x : ℝ => logb 2 μ * x ^ (31 / 32 : ℝ) + 2 * (x ^ (31 / 32 : ℝ) * logb 2 x)) =o[at_top] id
      by exact this.comp_tendsto tendsto_nat_cast_atTop_atTop
    refine' is_o.add (is_o.const_mul_left _ _) (is_o.const_mul_left _ _)
    · simpa only [rpow_one] using is_o_rpow_rpow (show (31 / 32 : ℝ) < 1 by norm_num1)
    refine'
      (is_O.mul_is_o (is_O_refl (fun k : ℝ => (k : ℝ) ^ (31 / 32 : ℝ)) at_top)
            (is_o_logb_rpow_at_top (show (0 : ℝ) < 1 / 32 by norm_num1))).congr'
        eventually_eq.rfl _
    filter_upwards [eventually_gt_at_top (0 : ℝ)] with k hk
    rw [← rpow_add hk]
    norm_num1
    rw [rpow_one, id.def]
  intro k s β hβ' hβ hs
  cases' le_or_lt (s : ℝ) 0 with hs' hs'
  · rw [← Nat.cast_zero, Nat.cast_le, le_zero_iff] at hs' 
    rw [hs', Nat.cast_zero, MulZeroClass.zero_mul]
    exact norm_nonneg _
  cases' le_or_lt (logb 2 (μ / β)) 0 with hβ'' hβ''
  · refine' (norm_nonneg _).trans' (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hβ'')
  have : 0 < k := by
    rw [pos_iff_ne_zero]
    rintro rfl
    refine' hs'.not_le (hs.trans _)
    norm_num
  refine' (mul_le_mul_of_nonneg_right hs hβ''.le).trans ((le_norm_self _).trans' _)
  rw [mul_left_comm, mul_comm (logb 2 μ), ← mul_add, ← Nat.cast_two, ← logb_pow, Nat.cast_two, ←
    logb_mul]
  rotate_left
  · positivity
  · positivity
  refine' mul_le_mul_of_nonneg_left _ (by positivity)
  refine' logb_le_logb_of_le one_lt_two.le (div_pos hμ₀ hβ') _
  refine' (div_le_div_of_le_left hμ₀.le (by positivity) hβ).trans _
  rw [div_div_eq_mul_div, div_one]

theorem eleven_two_aux_error_two (μ : ℝ) (hμ₀ : 0 < μ) (f : ℕ → ℝ)
    (hf : f =o[atTop] fun i => (1 : ℝ)) :
    ∃ g : ℕ → ℝ,
      (g =o[atTop] fun i => (i : ℝ)) ∧
        ∀ᶠ k in atTop,
          ∀ s t : ℕ,
            ∀ β : ℝ,
              0 < β →
                s ≤ k →
                  t ≤ k →
                    (1 + f k) * (s / (s + t)) ≤ β →
                      (s : ℝ) * logb 2 (μ / β) ≤ (s : ℝ) * logb 2 (μ * (s + t) / s) + g k :=
  by
  have := (is_o_one_iff _).1 hf
  have := this.eventually (eventually_gt_nhds (show (-1 : ℝ) < 0 by norm_num1))
  refine' ⟨fun k => ‖(k * -logb 2 (1 + f k) : ℝ)‖, _, _⟩
  · rw [is_o_norm_left]
    refine'
      ((is_O_refl (fun x : ℕ => (x : ℝ)) at_top).mul_isLittleO
            (logb_one_add_o _ hf).neg_left).trans_isBigO
        _
    simp only [mul_one]
    exact is_O_refl _ _
  filter_upwards [tendsto_coe_nat_at_top_at_top.eventually this] with k hk s t β hβ hsk htk hβ'
  have : 0 < 1 + f k := by refine' (add_lt_add_left hk 1).trans_eq' (by norm_num1)
  rcases s.eq_zero_or_pos with (rfl | hs)
  · rw [Nat.cast_zero, MulZeroClass.zero_mul, MulZeroClass.zero_mul, zero_add]
    exact norm_nonneg _
  rw [← sub_le_iff_le_add', norm_eq_abs, ← mul_sub, abs_mul, Nat.abs_cast]
  refine' (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hsk) _).trans' _
  · exact abs_nonneg _
  refine' mul_le_mul_of_nonneg_left ((le_abs_self _).trans' _) (Nat.cast_nonneg _)
  rw [le_neg_iff_add_nonpos_left, ← logb_div, ← logb_mul this.ne']
  rotate_left
  · positivity
  · positivity
  · positivity
  refine' logb_nonpos one_lt_two (by positivity) _
  rw [div_div, mul_comm β, ← div_div, mul_div_assoc', div_le_one hβ, div_div_eq_mul_div,
    mul_div_mul_left _ _ hμ₀.ne']
  exact hβ'

theorem eleven_two (μ : ℝ) (hμ₀ : 0 < μ) (hμ₁ : μ < 1) :
    ∃ f : ℕ → ℝ,
      (f =o[atTop] fun i => (i : ℝ)) ∧
        ∀ᶠ k : ℕ in atTop,
          ∀ n : ℕ,
            2 ≤ n →
              ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                (¬∃ (m : Finset (Fin n)) (c : Fin 2), χ.MonochromaticOf m c ∧ ![k, k] c ≤ m.card) →
                  ∀ ini : BookConfig χ,
                    1 / 2 ≤ ini.p →
                      ⌊(n / 2 : ℝ)⌋₊ ≤ ini.X.card →
                        let s := (densitySteps μ k k ini).card
                        let t := (redSteps μ k k ini).card
                        logb 2 n ≤
                          k * logb 2 μ⁻¹ + t * logb 2 (1 - μ)⁻¹ + s * logb 2 (μ * (s + t) / s) +
                            f k :=
  by
  have hp₀ : (0 : ℝ) < 1 / 2 := by norm_num1
  obtain ⟨f₁, hf₁', hf₁⟩ := eleven_two_start μ hμ₀ hμ₁
  obtain ⟨f₂, hf₂', hf₂⟩ := eight_six μ hμ₁
  obtain ⟨f₃, hf₃', hf₃⟩ := eleven_two_aux_error_one' μ hμ₀
  obtain ⟨f₄, hf₄', hf₄⟩ := eleven_two_aux_error_one_other μ hμ₀
  obtain ⟨f₅, hf₅', hf₅⟩ := eleven_two_aux_error_two μ hμ₀ f₂ hf₂'
  specialize hf₂ μ (1 / 2) hμ₀ hp₀
  refine' ⟨fun k => f₁ k + max (f₄ k - -f₃ k) (f₅ k), _, _⟩
  · exact hf₁'.add (is_o.max (hf₄'.sub hf₃'.neg_left) hf₅')
  clear hf₁' hf₂' hf₅'
  filter_upwards [hf₁, hf₂, beta_pos μ μ _ hμ₀ hμ₁ hp₀, one_div_sq_le_beta μ μ _ hμ₀ hμ₁ hp₀, hf₅,
    eventually_gt_at_top 0] with k hf₁' hf₂' hβ hβ' hf₅' hk₀ n hn'' χ hχ ini hini hn'
  clear hf₁ hf₂ hf₅
  have hsk : (density_steps μ k k ini).card ≤ k :=
    (four_four_blue_density μ hk₀.ne' hk₀.ne' hχ ini).trans' le_add_self
  have htk : (red_steps μ k k ini).card ≤ k := four_four_red μ hχ ini
  specialize hf₁' n hn'' χ hχ ini hini hn'
  specialize hf₂' k le_rfl μ le_rfl le_rfl n χ hχ ini hini
  specialize hβ k le_rfl μ le_rfl le_rfl n χ ini hini
  specialize hβ' k le_rfl μ le_rfl le_rfl n χ ini hini
  specialize hf₃ k (density_steps μ k k ini).card (red_steps μ k k ini).card htk
  specialize hf₄ k (density_steps μ k k ini).card (beta μ k k ini) hβ hβ'
  specialize hf₅' (density_steps μ k k ini).card (red_steps μ k k ini).card _ hβ hsk htk
  have : (0 : ℝ) < n := by positivity
  have hμ₁' : 0 < 1 - μ := sub_pos_of_lt hμ₁
  refine' ((logb_le_logb one_lt_two this (this.trans_le hf₁')).2 hf₁').trans _
  rw [logb_mul, logb_mul, logb_mul, logb_rpow two_pos, logb_pow, logb_pow, logb_pow, add_right_comm,
    add_right_comm _ (_ * logb _ (1 - μ)⁻¹), add_right_comm _ (_ * logb _ (1 - μ)⁻¹),
    add_le_add_iff_right, add_assoc, add_left_comm, add_assoc, add_le_add_iff_left, add_left_comm,
    add_le_add_iff_left, ← sub_le_iff_le_add']
  rotate_left
  · norm_num1
  · positivity
  · positivity
  · positivity
  · positivity
  · positivity
  · positivity
  cases' le_total ((density_steps μ k k ini).card : ℝ) (k ^ (31 / 32 : ℝ)) with hk hk
  · refine' (le_max_left _ _).trans' _
    refine' sub_le_sub (hf₄ hk) _
    exact (abs_le.1 (hf₃ hk)).1
  · refine' (le_max_right _ _).trans' _
    rw [sub_le_iff_le_add']
    exact hf₅' (hf₂' hk)

theorem y_small {μ k n} {χ : TopEdgeLabelling (Fin n) (Fin 2)} {ini : BookConfig χ}
    (hχ : ¬∃ (m : Finset (Fin n)) (c : Fin 2), χ.MonochromaticOf m c ∧ ![k, k] c ≤ m.card) {i : ℕ}
    (hi : i ≤ finalStep μ k k ini) :
    (algorithm μ k k ini i).y.card ≤
      ramseyNumber ![k, k - (redSteps μ k k ini ∩ Finset.range i).card] :=
  by
  rw [ramsey_number_pair_swap]
  by_contra' h'
  obtain ⟨m, hm⟩ := ramsey_number_le_finset h'.le χ
  simp only [Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    tsub_le_iff_right] at hm 
  rcases hm with ⟨⟩
  swap
  · exact hχ ⟨m, 1, hm.2⟩
  refine' hχ ⟨m ∪ (algorithm μ k k ini i).A, 0, _, hm.2.2.trans _⟩
  · rw [Finset.coe_union, top_edge_labelling.monochromatic_of_union]
    refine' ⟨hm.2.1, (algorithm μ k k ini i).red_a, _⟩
    refine' (algorithm μ k k ini i).red_XYA.subset_left _
    exact hm.1.trans (Finset.subset_union_right _ _)
  rw [Finset.card_union_eq]
  · exact add_le_add_left (four_four_red_aux _ _ hi) _
  exact (algorithm μ k k ini i).hYA.mono_left hm.1

theorem eleven_three (μ : ℝ) (hμ₀ : 0 < μ) (hμ₁ : μ < 1) :
    ∃ f : ℕ → ℝ,
      (f =o[atTop] fun i => (i : ℝ)) ∧
        ∀ᶠ k : ℕ in atTop,
          ∀ n : ℕ,
            2 ≤ n →
              ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                (¬∃ (m : Finset (Fin n)) (c : Fin 2), χ.MonochromaticOf m c ∧ ![k, k] c ≤ m.card) →
                  ∀ ini : BookConfig χ,
                    1 / 2 ≤ ini.p →
                      ⌊(n / 2 : ℝ)⌋₊ ≤ ini.y.card →
                        ∀ i : ℕ,
                          i ≤ finalStep μ k k ini →
                            let s := (densitySteps μ k k ini).card
                            let t := (redSteps μ k k ini ∩ Finset.range i).card
                            logb 2 n ≤ logb 2 (ramseyNumber ![k, k - t]) + s + t + f k :=
  by
  have hp₀ : (0 : ℝ) < 1 / 2 := by norm_num1
  obtain ⟨f, hf, hf'⟩ := six_one_general _ hp₀
  specialize hf' _ _ hμ₀ hμ₁
  refine' ⟨fun k => -(f k + -2), _, _⟩
  · refine' is_o.neg_left (is_o.add hf _)
    exact is_o_const_thing
  filter_upwards [hf', eventually_gt_at_top 0] with k hf hk₀ n hn χ hχ ini hini hn' i hi
  clear hf'
  specialize hf k le_rfl μ le_rfl le_rfl n χ hχ ini hini i hi
  replace hf := hf.trans (Nat.cast_le.2 (Y_small hχ hi))
  rw [mul_right_comm] at hf 
  have :
    2 ^
        (-((red_steps μ k k ini ∩ Finset.range i).card +
              (density_steps μ k k ini ∩ Finset.range i).card :
            ℝ)) ≤
      ini.p ^
        ((red_steps μ k k ini ∩ Finset.range i).card +
          (density_steps μ k k ini ∩ Finset.range i).card) :=
    by
    rw [rpow_neg two_pos.le, ← inv_rpow two_pos.le, ← Nat.cast_add, rpow_nat_cast]
    refine' pow_le_pow_of_le_left (by norm_num1) _ _
    rwa [← one_div]
  replace hf := hf.trans' (mul_le_mul_of_nonneg_left this (by positivity))
  rw [mul_right_comm, ← rpow_add two_pos] at hf 
  replace hf := hf.trans' (mul_le_mul_of_nonneg_left (large_X _ _ hn hn') (by positivity))
  rw [← mul_assoc, ← rpow_add two_pos] at hf 
  replace hf := logb_le_logb_of_le one_le_two (by positivity) hf
  rw [logb_mul, logb_rpow two_pos one_lt_two.ne', ← le_sub_iff_add_le'] at hf 
  rotate_left
  · positivity
  · positivity
  refine' hf.trans _
  rw [add_assoc, add_left_comm, ← sub_sub, sub_neg_eq_add, ← sub_eq_add_neg _ (f k + -2), ←
    add_assoc, add_right_comm, add_sub_assoc, add_sub_assoc]
  refine' add_le_add_right (add_le_add_left _ _) _
  refine' Nat.cast_le.2 (Finset.card_le_of_subset _)
  exact Finset.inter_subset_left _ _

theorem eleven_three_special (μ : ℝ) (hμ₀ : 0 < μ) (hμ₁ : μ < 1) :
    ∃ f : ℕ → ℝ,
      (f =o[atTop] fun i => (i : ℝ)) ∧
        ∀ᶠ k : ℕ in atTop,
          ∀ n : ℕ,
            2 ≤ n →
              ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                (¬∃ (m : Finset (Fin n)) (c : Fin 2), χ.MonochromaticOf m c ∧ ![k, k] c ≤ m.card) →
                  ∀ ini : BookConfig χ,
                    1 / 2 ≤ ini.p →
                      ⌊(n / 2 : ℝ)⌋₊ ≤ ini.y.card →
                        let s := (densitySteps μ k k ini).card
                        let t := (redSteps μ k k ini).card
                        logb 2 n ≤ logb 2 (ramseyNumber ![k, k - t]) + s + t + f k :=
  by
  obtain ⟨f, hf, hf'⟩ := eleven_three μ hμ₀ hμ₁
  refine' ⟨f, hf, _⟩
  filter_upwards [hf'] with k hf n hn χ hχ ini hini hn'
  specialize hf n hn χ hχ ini hini hn' _ le_rfl
  have : red_steps μ k k ini ∩ Finset.range (final_step μ k k ini) = red_steps μ k k ini :=
    by
    rw [Finset.inter_eq_left_iff_subset]
    exact red_steps_subset_red_or_density_steps.trans (Finset.filter_subset _ _)
  rwa [this] at hf 

theorem ramseyNumber_diag_ge {k : ℕ} (hk : 2 ≤ k) : k ≤ ramseyNumber ![k, k] :=
  by
  refine' (ramsey_number.mono_two hk le_rfl).trans' _
  simp only [ramsey_number_cons_two, ramsey_number_singleton]

theorem two_le_n_of_large_k {k : ℕ} (hk : 4 ≤ k) : 2 ≤ ⌈(ramseyNumber ![k, k] : ℝ) / 2⌉₊ :=
  by
  refine' Nat.cast_le.1 ((Nat.le_ceil _).trans' _)
  rw [Nat.cast_two, le_div_iff (zero_lt_two' ℝ)]
  have : k ≤ ramsey_number ![k, k] := ramsey_number_diag_ge (hk.trans' (show 2 ≤ 4 by norm_num))
  refine' (Nat.cast_le.2 (hk.trans this)).trans' _
  norm_num1

theorem compRight_labelGraph_apply {V K K' : Type _} {k : K} {χ : TopEdgeLabelling V K} (f : K → K')
    (hf : Function.Injective f) : (χ.compRight f).labelGraph (f k) = χ.labelGraph k :=
  by
  ext x y
  simp only [top_edge_labelling.label_graph_adj, top_edge_labelling.comp_right_get, hf.eq_iff]

theorem compRight_density_apply {V K K' : Type _} [Fintype V] [DecidableEq V] [DecidableEq K]
    [DecidableEq K'] (k : K) {χ : TopEdgeLabelling V K} (f : K → K') (hf : Function.Injective f) :
    (χ.compRight f).density (f k) = χ.density k :=
  by
  rw [top_edge_labelling.density, top_edge_labelling.density, Rat.cast_inj]
  exact density_congr _ _ (comp_right_label_graph_apply _ hf)

theorem density_sum {V : Type _} [Fintype V] [DecidableEq V] (hV : 2 ≤ Fintype.card V)
    (χ : TopEdgeLabelling V (Fin 2)) : χ.density 0 + (χ.compRight (Equiv.swap 0 1)).density 0 = 1 :=
  by
  have : (χ.comp_right (Equiv.swap 0 1)).density 0 = χ.density 1 :=
    by
    have : Equiv.swap (0 : Fin 2) 1 1 = 0 := by simp only [Equiv.swap_apply_right, eq_self_iff_true]
    rw [← comp_right_density_apply 1 (Equiv.swap (0 : Fin 2) 1), this]
    exact Equiv.injective _
  rwa [this, density_zero_one, sub_add_cancel]

theorem density_nonneg {V : Type _} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : 0 ≤ G.density := by rw [SimpleGraph.density]; positivity

theorem some_large_density {V : Type _} [Fintype V] [DecidableEq V] (hV : 2 ≤ Fintype.card V)
    (χ : TopEdgeLabelling V (Fin 2)) :
    1 / 2 ≤ χ.density 0 ∨ 1 / 2 ≤ (χ.compRight (Equiv.swap 0 1)).density 0 :=
  by
  have := density_sum hV χ
  have : 0 ≤ χ.density 0 := Rat.cast_nonneg.2 (density_nonneg _)
  have : 0 ≤ (χ.comp_right (Equiv.swap 0 1)).density 0 := Rat.cast_nonneg.2 (density_nonneg _)
  by_contra'
  linarith

theorem eleven_one_one {m : ℕ} (hm : 2 ≤ m) : ⌈(m : ℝ) / 2⌉₊ < m :=
  by
  refine' Nat.cast_lt.1 ((ceil_lt_two_mul _).trans_le _)
  · refine' div_lt_div_of_lt two_pos _
    rw [Nat.one_lt_cast]
    exact hm
  rw [mul_div_cancel']
  norm_num1

/-- The function `G` from the paper. -/
noncomputable def g (μ x y : ℝ) : ℝ :=
  logb 2 μ⁻¹ + x * logb 2 (1 - μ)⁻¹ + y * logb 2 (μ * ((x + y) / y))

theorem eleven_two_improve (μ : ℝ) (hμ₀ : 0 < μ) (hμ₁ : μ < 1) :
    ∃ f : ℕ → ℝ,
      (f =o[atTop] fun i => (i : ℝ)) ∧
        ∀ᶠ k : ℕ in atTop,
          ∀ n : ℕ,
            2 ≤ n →
              ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                (¬∃ (m : Finset (Fin n)) (c : Fin 2), χ.MonochromaticOf m c ∧ ![k, k] c ≤ m.card) →
                  ∀ ini : BookConfig χ,
                    1 / 2 ≤ ini.p →
                      ⌊(n / 2 : ℝ)⌋₊ ≤ ini.X.card →
                        let s := (densitySteps μ k k ini).card
                        let t := (redSteps μ k k ini).card
                        logb 2 n ≤ k * g μ (t / k) (s / k) + f k :=
  by
  obtain ⟨f, hf, hf'⟩ := eleven_two μ hμ₀ hμ₁
  refine' ⟨f, hf, _⟩
  filter_upwards [hf', eventually_gt_at_top 0] with k hf hk₀ n hn χ hχ ini hini hnX
  clear hf'
  specialize hf n hn χ hχ ini hini hnX
  refine' hf.trans _
  clear hf
  rw [G, add_le_add_iff_right, mul_div_assoc, mul_add, mul_add, ← mul_assoc, mul_div_cancel',
    add_le_add_iff_left, ← mul_assoc, mul_div_cancel', ← add_div, div_div_div_cancel_right,
    add_comm]
  · positivity
  · positivity
  · positivity

theorem sInf_mem_of_upclosed {s : Set ℝ} {ε : ℝ} (hf' : s.Nonempty)
    (hf'' : ∀ x ∈ s, ∀ y, x ≤ y → y ∈ s) (hε : 0 < ε) : sInf s + ε ∈ s :=
  by
  by_contra' hε'
  have : ∀ x ∈ s, Inf s + ε < x := by
    intro x hx
    by_contra'
    exact hε' (hf'' _ hx _ this)
  have : Inf s + ε ≤ Inf s := le_csInf hf' fun x hx => (this _ hx).le
  simp only [add_le_iff_nonpos_right] at this 
  exact hε.not_le this

theorem le_limsup_add (f : ℕ → ℝ) (hf : BddAbove (Set.range f)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x in atTop, f x ≤ limsup f atTop + ε :=
  by
  suffices limsup f at_top + ε ∈ {a : ℝ | ∀ᶠ n : ℕ in at_top, f n ≤ a} by exact this
  simp only [limsup_eq]
  refine' Inf_mem_of_upclosed _ _ hε
  · obtain ⟨y, hy⟩ := hf
    refine' ⟨y, eventually_of_forall _⟩
    intro z
    exact hy ⟨z, rfl⟩
  intro x hx y hxy
  filter_upwards [hx] with z hz using hz.trans hxy

theorem exists_nice_χ {k n : ℕ} (hn2 : 2 ≤ n) (hnr : n < ramseyNumber ![k, k]) :
    ∃ χ : TopEdgeLabelling (Fin n) (Fin 2),
      1 / 2 ≤ χ.density 0 ∧
        ¬∃ (m : Finset (Fin n)) (c : Fin 2), χ.MonochromaticOf m c ∧ ![k, k] c ≤ m.card :=
  by
  rw [← not_le, ramsey_number_le_iff_fin, is_ramsey_valid, Classical.not_forall] at hnr 
  obtain ⟨χ : top_edge_labelling (Fin n) (Fin 2), hχ⟩ := hnr
  wlog hχ' : 1 / 2 ≤ χ.density 0 generalizing χ
  · have hd : 1 / 2 ≤ χ.density 0 ∨ 1 / 2 ≤ (χ.comp_right (Equiv.swap 0 1)).density 0 :=
      some_large_density (hn2.trans_eq (Fintype.card_fin _).symm) _
    refine' this (χ.comp_right (Equiv.swap 0 1)) _ (hd.resolve_left hχ')
    simp only [Fin.exists_fin_two, top_edge_labelling.monochromatic_of, Finset.mem_coe,
      top_edge_labelling.comp_right_get, Equiv.apply_eq_iff_eq_symm_apply, Ne.def, Equiv.symm_swap,
      Equiv.swap_apply_left, Matrix.cons_val_zero, Equiv.swap_apply_right, Matrix.cons_val_one,
      Matrix.head_cons, not_exists, not_or] at hχ ⊢
    intro x
    exact (hχ x).symm
  exact ⟨χ, hχ', hχ⟩

theorem exists_nicer_χ (k : ℕ) :
    ∃ χ : TopEdgeLabelling (Fin ⌈(ramseyNumber ![k, k] : ℝ) / 2⌉₊) (Fin 2),
      4 ≤ k →
        1 / 2 ≤ χ.density 0 ∧
          ¬∃ (m : Finset (Fin ⌈(ramseyNumber ![k, k] : ℝ) / 2⌉₊)) (c : Fin 2),
              χ.MonochromaticOf m c ∧ ![k, k] c ≤ m.card :=
  by
  cases' lt_or_le k 4 with hk hk
  · exact ⟨top_edge_labelling.mk (fun _ _ _ => 0) (by simp), fun h => False.elim (hk.not_le h)⟩
  let n := ⌈(ramsey_number ![k, k] : ℝ) / 2⌉₊
  have hn2 : 2 ≤ n := two_le_n_of_large_k hk
  have hnr : n < ramsey_number ![k, k] :=
    by
    refine' eleven_one_one _
    have : 2 ≤ k := hk.trans' (by norm_num1)
    exact (ramsey_number_diag_ge this).trans_lt' this
  obtain ⟨χ, hχ, hχ'⟩ := exists_nice_χ hn2 hnr
  exact ⟨χ, fun _ => ⟨hχ, hχ'⟩⟩

/-- Get a choice of colouring with the appropriate properties: more than half red edges and no
monochromatic cliques of size k.
-/
noncomputable def getχ (k : ℕ) : TopEdgeLabelling (Fin ⌈(ramseyNumber ![k, k] : ℝ) / 2⌉₊) (Fin 2) :=
  (exists_nicer_χ k).some

theorem getχ_density {k : ℕ} (hk : 4 ≤ k) : 1 / 2 ≤ (getχ k).density 0 :=
  ((exists_nicer_χ k).choose_spec hk).1

theorem getχ_ramsey {k : ℕ} (hk : 4 ≤ k) :
    ¬∃ (m : Finset (Fin ⌈(ramseyNumber ![k, k] : ℝ) / 2⌉₊)) (c : Fin 2),
        (getχ k).MonochromaticOf m c ∧ ![k, k] c ≤ m.card :=
  ((exists_nicer_χ k).choose_spec hk).2

theorem exists_nicer_ini (k : ℕ) :
    ∃ ini : BookConfig (getχ k),
      4 ≤ k →
        (getχ k).density 0 ≤ ini.p ∧
          ⌊(⌈(ramseyNumber ![k, k] : ℝ) / 2⌉₊ / 2 : ℝ)⌋₊ ≤ ini.X.card ∧
            ⌊(⌈(ramseyNumber ![k, k] : ℝ) / 2⌉₊ / 2 : ℝ)⌋₊ ≤ ini.y.card :=
  by
  cases' lt_or_le k 4 with hk hk
  · refine' ⟨_, fun h => False.elim (hk.not_le h)⟩
    refine' ⟨∅, ∅, ∅, ∅, _, _, _, _, _, _, _, _, _, _⟩
    all_goals simp
  set n := ⌈(ramsey_number ![k, k] : ℝ) / 2⌉₊
  have hn2 : 2 ≤ n := two_le_n_of_large_k hk
  obtain ⟨ini, hini, hiniX, hiniY⟩ := exists_equibipartition_col_density (get_χ k) hn2
  exact ⟨ini, fun _ => ⟨hini, hiniX, hiniY⟩⟩

/-- Get the start configuration which has the appropriate density and sizes -/
noncomputable def getIni (k : ℕ) : BookConfig (getχ k) :=
  (exists_nicer_ini k).some

theorem getIni_p {k : ℕ} (hk : 4 ≤ k) : (getχ k).density 0 ≤ (getIni k).p :=
  ((exists_nicer_ini k).choose_spec hk).1

theorem getIni_card_x {k : ℕ} (hk : 4 ≤ k) :
    ⌊(⌈(ramseyNumber ![k, k] : ℝ) / 2⌉₊ / 2 : ℝ)⌋₊ ≤ (getIni k).X.card :=
  ((exists_nicer_ini k).choose_spec hk).2.1

theorem getIni_card_y {k : ℕ} (hk : 4 ≤ k) :
    ⌊(⌈(ramseyNumber ![k, k] : ℝ) / 2⌉₊ / 2 : ℝ)⌋₊ ≤ (getIni k).y.card :=
  ((exists_nicer_ini k).choose_spec hk).2.2

theorem getIni_p' {k : ℕ} (hk : 4 ≤ k) : 1 / 2 ≤ (getIni k).p :=
  (getχ_density hk).trans ((exists_nicer_ini k).choose_spec hk).1

theorem R_k_close_to_n (k : ℕ) (hk₆ : 4 ≤ k) :
    logb 2 (ramseyNumber ![k, k]) - 1 ≤ logb 2 ⌈(ramseyNumber ![k, k] : ℝ) / 2⌉₊ :=
  by
  have hn2 := two_le_n_of_large_k hk₆
  rw [le_logb_iff_rpow_le one_lt_two, rpow_sub two_pos, rpow_logb two_pos one_lt_two.ne', rpow_one]
  · exact Nat.le_ceil _
  · rw [Nat.cast_pos]
    refine' (ramsey_number_diag_ge (hk₆.trans' (by norm_num1))).trans_lt' _
    positivity
  rw [Nat.cast_pos]
  positivity

theorem bin_ent_deriv_aux (x : ℝ) (hx₀ : x ≠ 0) (hx₁ : x ≠ 1) :
    HasDerivAt (fun y => -(y * log y) + -((1 - y) * log (1 - y))) (log (1 - x) - log x) x :=
  by
  have h : ∀ x : ℝ, x ≠ 0 → HasDerivAt (fun y => -(y * log y)) (-(log x + 1)) x :=
    by
    rintro x hx₀
    refine' HasDerivAt.neg _
    have : 1 * log x + x * x⁻¹ = log x + 1 := by rw [one_mul, mul_inv_cancel hx₀]
    rw [← this]
    exact HasDerivAt.mul (hasDerivAt_id' x) (has_deriv_at_log hx₀)
  suffices
    HasDerivAt (fun y => -(y * log y) + -((1 - y) * log (1 - y)))
      (-(log x + 1) + -(log (1 - x) + 1) * -1) x
    by
    convert this using 1
    ring_nf
  have : HasDerivAt (fun y : ℝ => 1 - y) (-1 : ℝ) x := (hasDerivAt_id' x).const_sub 1
  refine' HasDerivAt.add (h _ hx₀) _
  exact (h (1 - x) (sub_ne_zero_of_ne hx₁.symm)).comp x ((hasDerivAt_id' x).const_sub 1)

theorem binEnt_deriv (b x : ℝ) (hx₀ : x ≠ 0) (hx₁ : x ≠ 1) :
    HasDerivAt (binEnt b) (logb b (1 - x) - logb b x) x :=
  by
  convert HasDerivAt.div_const (bin_ent_deriv_aux x hx₀ hx₁) (log b) using 1
  · ext y
    rw [binEnt_eq]
  rw [logb, logb, sub_div]

theorem strictMonoOn_binEnt_zero_half_aux {b : ℝ} (hb : 1 < b) :
    StrictMonoOn (binEnt b) (Set.Ioc 0 (1 / 2)) :=
  by
  suffices StrictMonoOn (fun p => -(p * log p) + -((1 - p) * log (1 - p))) (Set.Ioc 0 (1 / 2))
    by
    intro x hx x' hx' h
    rw [binEnt_eq, binEnt_eq]
    exact div_lt_div_of_lt (log_pos hb) (this hx hx' h)
  clear hb b
  refine'
    Convex.strictMonoOn_of_hasDerivAt_pos (convex_Ioc _ _)
      (fun x hx => bin_ent_deriv_aux x hx.1.ne' (by linarith only [hx.2])) _
  rw [interior_Ioc]
  rintro x ⟨hx₁, hx₂⟩
  rw [sub_pos]
  refine' log_lt_log _ _ <;> linarith only [hx₁, hx₂]

theorem strictMonoOn_binEnt_zero_half {b : ℝ} (hb : 1 < b) :
    StrictMonoOn (binEnt b) (Set.Icc 0 (1 / 2)) :=
  by
  rintro x ⟨hx₁, hx₂⟩ y ⟨hy₁, hy₂⟩ h
  rcases lt_or_eq_of_le hx₁ with (hx₁ | rfl)
  · exact strict_mono_on_bin_ent_zero_half_aux hb ⟨hx₁, hx₂⟩ ⟨hx₁.trans h, hy₂⟩ h
  rw [binEnt_zero]
  refine'
    (strict_mono_on_bin_ent_zero_half_aux hb ⟨half_pos h, by linarith⟩ ⟨h, hy₂⟩
          (half_lt_self h)).trans_le'
      _
  exact binEnt_nonneg hb (by linarith) (by linarith)

theorem strictAntiOn_binEnt_half_one {b : ℝ} (hb : 1 < b) :
    StrictAntiOn (binEnt b) (Set.Icc (1 / 2) 1) :=
  by
  rintro x ⟨hx₁, hx₂⟩ y ⟨hy₁, hy₂⟩ h
  have :=
    strict_mono_on_bin_ent_zero_half hb ⟨sub_nonneg_of_le hy₂, by linarith⟩
      ⟨sub_nonneg_of_le hx₂, by linarith⟩ (sub_lt_sub_left h _)
  rw [binEnt_symm, binEnt_symm] at this 
  exact this

theorem strictMonoOn_Icc_iff {f : ℝ → ℝ} {a b : ℝ} :
    StrictMonoOn f (Set.Icc a b) ↔ ∀ x y, a ≤ x → x < y → y ≤ b → f x < f y :=
  by
  constructor
  · intro h x y hax hxy hyb
    exact h ⟨hax, hxy.le.trans hyb⟩ ⟨hax.trans hxy.le, hyb⟩ hxy
  rintro h x ⟨hx₁, hx₂⟩ y ⟨hy₁, hy₂⟩ hxy
  exact h _ _ hx₁ hxy hy₂

theorem strictAntiOn_Icc_iff {f : ℝ → ℝ} {a b : ℝ} :
    StrictAntiOn f (Set.Icc a b) ↔ ∀ x y, a ≤ x → x < y → y ≤ b → f y < f x :=
  by
  constructor
  · intro h x y hax hxy hyb
    exact h ⟨hax, hxy.le.trans hyb⟩ ⟨hax.trans hxy.le, hyb⟩ hxy
  rintro h x ⟨hx₁, hx₂⟩ y ⟨hy₁, hy₂⟩ hxy
  exact h _ _ hx₁ hxy hy₂

theorem antitoneOn_Icc_iff {f : ℝ → ℝ} {a b : ℝ} :
    AntitoneOn f (Set.Icc a b) ↔ ∀ x y, a ≤ x → x ≤ y → y ≤ b → f y ≤ f x :=
  by
  constructor
  · intro h x y hax hxy hyb
    exact h ⟨hax, hxy.trans hyb⟩ ⟨hax.trans hxy, hyb⟩ hxy
  rintro h x ⟨hx₁, hx₂⟩ y ⟨hy₁, hy₂⟩ hxy
  exact h _ _ hx₁ hxy hy₂

/-- Function f1 from the paper -/
noncomputable def f1 (x y : ℝ) : ℝ :=
  x + y + (2 - x) * binEnt 2 (1 / (2 - x))

/-- Function f2 from the paper -/
noncomputable def f2 (x y : ℝ) : ℝ :=
  x + y + (2 - x) * binEnt 2 (1 / (2 - x)) - 1 / (log 2 * 40) * ((1 - x) / (2 - x))

/-- Function f from the paper -/
noncomputable def f (x y : ℝ) : ℝ :=
  if 3 / 4 ≤ x then f2 x y else f1 x y

/- warning: simple_graph.g clashes with simple_graph.G -> SimpleGraph.g
Case conversion may be inaccurate. Consider using '#align simple_graph.g SimpleGraph.gₓ'. -/
#print SimpleGraph.g /-
/-- Function g from the paper -/
noncomputable def g (x y : ℝ) : ℝ :=
  g (2 / 5) x y
-/

theorem f_eq (x y : ℝ) :
    f x y = f1 x y - if 3 / 4 ≤ x then 1 / (log 2 * 40) * ((1 - x) / (2 - x)) else 0 :=
  by
  rw [f, f1, f2]
  split_ifs
  · rfl
  rw [sub_zero]

theorem g_eq (x y : ℝ) :
    g x y = logb 2 (5 / 2) + x * logb 2 (5 / 3) + y * logb 2 (2 / 5 * ((x + y) / y)) := by
  rw [g, G]; norm_num

-- noncomputable def F (k : ℕ) (x y : ℝ) : ℝ :=
--   x + y + logb 2 (ramsey_number ![k, ⌊(k : ℝ) - x * k⌋₊]) / k
theorem twelve_one {b' : ℝ} (hb' : 1 < b') {a b : ℕ} (h : b ≤ a) :
    logb b' (a.choose b) ≤ a * binEnt b' (b / a) :=
  by
  rcases b.eq_zero_or_pos with (rfl | hb)
  ·
    simp only [Nat.choose_zero_right, Nat.cast_one, logb_one, Nat.cast_zero, zero_div, binEnt_zero,
      MulZeroClass.mul_zero]
  rcases eq_or_lt_of_le h with (rfl | hab)
  · rw [div_self]
    · simp
    positivity
  have : 0 < a := hb.trans_le h
  have : 0 < (1 - b / a : ℝ) := sub_pos_of_lt ((div_lt_one (by positivity)).2 (Nat.cast_lt.2 hab))
  have : (b / a : ℝ) ^ b * (1 - b / a) ^ (a - b) * a.choose b ≤ 1 :=
    by
    have := add_pow (b / a : ℝ) (1 - b / a) a
    rw [add_sub_cancel'_right, one_pow] at this 
    refine' this.symm.trans_ge _
    have : b ∈ Finset.range (a + 1) := by rwa [Finset.mem_range_succ_iff]
    refine' (Finset.single_le_sum _ this).trans_eq' rfl
    · intro i hi
      positivity
  rwa [binEnt, mul_sub, ← mul_assoc, ← mul_assoc, mul_neg, mul_one_sub, mul_div_cancel',
    le_sub_iff_add_le, neg_mul, le_neg_iff_add_nonpos_left, ← logb_pow, ← Nat.cast_sub h, ←
    logb_pow, ← logb_mul, mul_comm, ← logb_mul, ← mul_assoc, logb_nonpos_iff' hb']
  · positivity
  · positivity
  · exact (mul_pos (by positivity) (Nat.cast_pos.2 (Nat.choose_pos h))).ne'
  · exact (Nat.cast_pos.2 (Nat.choose_pos h)).ne'
  · positivity
  · positivity

-- lemma ten_one_precise (γ₀ : ℝ) (hγ₀ : 0 < γ₀) :
--   ∀ᶠ l : ℕ in at_top, ∀ k : ℕ,
--   ∀ γ δ : ℝ, γ = l / (k + l) → γ₀ ≤ γ → γ ≤ 1 / 5 → δ = γ / 40 →
--   (ramsey_number ![k, l] : ℝ) ≤ exp (- δ * k + 2.05) * (k + l).choose l :=
-- lemma eleven_three (μ : ℝ) (hμ₀ : 0 < μ) (hμ₁ : μ < 1) :
--   ∃ f : ℕ → ℝ, f =o[at_top] (λ i, (i : ℝ)) ∧
--     ∀ᶠ k : ℕ in at_top,
--     ∀ n : ℕ, 2 ≤ n →
--     ∀ χ : top_edge_labelling (fin n) (fin 2),
--     ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, k] c ≤ m.card) →
--     ∀ (ini : book_config χ), 1 / 2 ≤ ini.p → ⌊(n / 2 : ℝ)⌋₊ ≤ ini.Y.card →
--     let s := (density_steps μ k k ini).card,
--         t := (red_steps μ k k ini).card
--     in logb 2 n ≤ logb 2 (ramsey_number ![k, k - t]) + s + t + f k :=
theorem y_le_x_hMul (μ η : ℝ) (hμ₀ : 0 < μ) (hμ₁ : μ < 1) (hη : 0 < η) :
    ∀ᶠ k : ℕ in atTop,
      ∀ n : ℕ,
        2 ≤ n →
          ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
            (¬∃ (m : Finset (Fin n)) (c : Fin 2), χ.MonochromaticOf m c ∧ ![k, k] c ≤ m.card) →
              ∀ ini : BookConfig χ,
                1 / 2 ≤ ini.p →
                  let s := (densitySteps μ k k ini).card
                  let t := (redSteps μ k k ini).card
                  (s / k : ℝ) ≤ μ / (1 - μ) * (t / k) + η :=
  by
  have hp₀ : (0 : ℝ) < 1 / 2 := by norm_num1
  have : (fun k : ℕ => 7 / (1 - μ) * k ^ (15 / 16 : ℝ)) =o[at_top] fun k : ℕ => (k : ℝ) :=
    by
    refine' is_o.const_mul_left _ _
    suffices (fun k : ℝ => k ^ (15 / 16 : ℝ)) =o[at_top] id by
      exact is_o.comp_tendsto this tendsto_nat_cast_atTop_atTop
    simpa only [rpow_one] using is_o_rpow_rpow (show (15 / 16 : ℝ) < 1 by norm_num)
  filter_upwards [eight_five _ _ _ hμ₀ hμ₁ hp₀, beta_pos _ _ _ hμ₀ hμ₁ hp₀,
    beta_le_μ _ _ _ hμ₀ hμ₁ hp₀, this.bound hη, eventually_gt_at_top 0] with k h₈₅ hβ₀ hβμ hη' hk₀ n
    hn χ hχ ini hini
  specialize h₈₅ k le_rfl μ le_rfl le_rfl n χ hχ ini hini
  specialize hβ₀ k le_rfl _ le_rfl le_rfl n χ ini hini
  specialize hβμ _ le_rfl _ le_rfl le_rfl n χ ini hini
  rw [div_le_iff, add_mul, mul_assoc, div_mul_cancel]
  rotate_left
  · positivity
  · positivity
  refine' h₈₅.trans (add_le_add _ _)
  · refine' mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    rwa [div_le_div_iff, mul_one_sub, mul_one_sub, mul_comm, sub_le_sub_iff_right]
    · exact sub_pos_of_lt (hβμ.trans_lt hμ₁)
    · exact sub_pos_of_lt hμ₁
  · rw [norm_eq_abs, norm_coe_nat] at hη' 
    exact (le_abs_self _).trans hη'

theorem x_le_1 :
    ∀ᶠ k : ℕ in atTop,
      ∀ n : ℕ,
        2 ≤ n →
          ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
            (¬∃ (m : Finset (Fin n)) (c : Fin 2), χ.MonochromaticOf m c ∧ ![k, k] c ≤ m.card) →
              ∀ ini : BookConfig χ,
                1 / 2 ≤ ini.p →
                  let t := (redSteps (2 / 5) k k ini).card
                  t ≤ k ∧ (t / k : ℝ) ≤ 1 :=
  by
  have hμ₀ : (0 : ℝ) < 2 / 5 := by norm_num1
  have hμ₁ : (2 / 5 : ℝ) < 1 := by norm_num1
  filter_upwards [eventually_gt_at_top 0] with k hk₀ n hn2 χ hχ ini hini
  suffices (red_steps (2 / 5) k k ini).card ≤ k
    by
    refine' ⟨this, div_le_one_of_le _ (Nat.cast_nonneg _)⟩
    rwa [Nat.cast_le]
  exact four_four_red _ hχ _

theorem y_le_3_4 :
    ∀ᶠ k : ℕ in atTop,
      ∀ n : ℕ,
        2 ≤ n →
          ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
            (¬∃ (m : Finset (Fin n)) (c : Fin 2), χ.MonochromaticOf m c ∧ ![k, k] c ≤ m.card) →
              ∀ ini : BookConfig χ,
                1 / 2 ≤ ini.p →
                  let s := (densitySteps (2 / 5) k k ini).card
                  (s / k : ℝ) ≤ 0.75 :=
  by
  have hμ₀ : (0 : ℝ) < 2 / 5 := by norm_num1
  have hμ₁ : (2 / 5 : ℝ) < 1 := by norm_num1
  have hη : (0 : ℝ) < 1 / 12 := by norm_num1
  filter_upwards [y_le_x_mul (2 / 5) (1 / 12) hμ₀ hμ₁ hη, eventually_gt_at_top 0] with k hk hk₀ n
    hn2 χ hχ ini hini
  specialize hk n hn2 χ hχ ini hini
  refine' hk.trans _
  have : ((red_steps (2 / 5) k k ini).card : ℝ) / k ≤ 1 :=
    by
    refine' div_le_one_of_le _ (Nat.cast_nonneg _)
    rw [Nat.cast_le]
    exact four_four_red _ hχ _
  norm_num1
  linarith only [this]

section

theorem bin_ent_hundredth_left : logb 2 (1 / 100)⁻¹ ≤ 20 / 3 :=
  by
  rw [inv_div, div_one, le_div_iff, mul_comm]
  have : logb 2 (100 ^ 3) = 3 * logb 2 100 :=
    by
    rw [logb_pow]
    norm_num
  rw [← this, logb_le_iff_le_rpow one_lt_two]
  · norm_num1
  · norm_num1
  · norm_num1

theorem bin_ent_hundredth_right : 99 * logb 2 ((100 - 1) / 100)⁻¹ ≤ 1.5 :=
  by
  have : ((100 - 1 : ℝ) / 100)⁻¹ = 1 + 1 / 99 := by norm_num1
  rw [this, logb, mul_div_assoc', div_le_iff (log_pos one_lt_two)]
  have : log (1 + 1 / 99) ≤ 1 / 99 :=
    by
    rw [add_comm, log_le_iff_le_exp]
    · exact add_one_le_exp _
    · norm_num1
  have : 1 ≤ 3 / 2 * log 2 := by
    rw [← div_le_iff']
    refine' log_two_gt_d9.le.trans' (by norm_num1)
    norm_num1
  linarith

theorem binEnt_hundredth : binEnt 2 1e-2 ≤ 0.1 :=
  by
  rw [binEnt, neg_mul, ← mul_neg, ← logb_inv, sub_eq_add_neg, ← mul_neg, ← logb_inv, one_sub_div]
  linarith only [bin_ent_hundredth_left, bin_ent_hundredth_right]
  norm_num1

end

-- lemma eq_62 :
-- 1 - 1 / (2 - x) = ((2 - x) - 1) / (2 - x) = (1 - x) / (2 - x)
theorem F_le_f1_aux {k t : ℕ} {x : ℝ} (hx : x = t / k) (hk : 0 < k) (hx1 : x ≤ 1) :
    logb 2 ((k + (k - t)).choose k) ≤ k * ((2 - x) * binEnt 2 (1 / (2 - x))) :=
  by
  have : t ≤ k := by
    contrapose! hx1
    rwa [hx, one_lt_div, Nat.cast_lt]
    rwa [Nat.cast_pos]
  refine' (twelve_one one_lt_two le_self_add).trans _
  have h₁ : (↑(k + (k - t)) : ℝ) = k * (2 - x) :=
    by
    rw [hx, mul_sub, mul_div_cancel', Nat.cast_add, Nat.cast_sub this]
    · ring_nf
    positivity
  rw [h₁, ← div_div, div_self, mul_assoc]
  positivity

theorem F_le_f1 {k t : ℕ} {x : ℝ} (hx : x = t / k) (hk : 0 < k) (hx1 : x ≤ 1) :
    logb 2 (ramseyNumber ![k, k - t]) ≤ k * ((2 - x) * binEnt 2 (1 / (2 - x))) :=
  by
  have : t ≤ k := by
    contrapose! hx1
    rwa [hx, one_lt_div, Nat.cast_lt]
    rwa [Nat.cast_pos]
  rcases eq_or_ne t k with (rfl | htk)
  · rw [div_self] at hx 
    rw [hx, ramsey_number_pair_swap]
    · norm_num
    positivity
  have : 0 < k - t := Nat.sub_pos_of_lt (lt_of_le_of_ne this htk)
  refine' (F_le_f1_aux hx hk hx1).trans' (logb_le_logb_of_le one_le_two _ _)
  · rw [Nat.cast_pos, ramsey_number_pos, Fin.forall_fin_two]
    exact ⟨hk.ne', this.ne'⟩
  rw [Nat.cast_le]
  exact ramsey_number_le_choose'

theorem eleven_one_special (η : ℝ) (hη : 0 < η) :
    ∀ᶠ k : ℕ in atTop,
      let t := (redSteps (2 / 5) k k (getIni k)).card
      let x := (t : ℝ) / k
      t ≤ k →
        0.75 ≤ x →
          x ≤ 0.99 →
            logb 2 (ramseyNumber ![k, k - t]) ≤
              k * ((2 - x) * binEnt 2 (1 / (2 - x)) - 1 / (log 2 * 40) * ((1 - x) / (2 - x)) + η) :=
  by
  have hγ₀ : (0 : ℝ) < 1 / 101 := by norm_num1
  have q :=
    (tendsto_nat_ceil_at_top.comp
          (tendsto_id.at_top_mul_const' (show (0 : ℝ) < 1e-2 by positivity))).comp
      tendsto_nat_cast_atTop_atTop
  filter_upwards [q.eventually (top_adjuster (ten_one_precise _ hγ₀)), eventually_gt_at_top 0,
    eventually_ge_at_top ⌈41 / 20 / log 2 / η⌉₊] with k hk hk₀ hkη htk hxl hxu
  set t := (red_steps (2 / 5) k k (get_ini k)).card
  set x := (t : ℝ) / k
  have h₁ : ⌈(k : ℝ) * (1 / 100)⌉₊ ≤ k - t :=
    by
    rw [Nat.ceil_le, Nat.cast_sub htk]
    rw [div_le_iff] at hxu 
    · linarith only [hxu]
    positivity
  have h2x : 0 < 2 - x := sub_pos_of_lt (hxu.trans_lt (by norm_num1))
  have h₂ : (↑(k - t) : ℝ) / (↑k + ↑(k - t)) = 1 - 1 / (2 - x) :=
    by
    rw [Nat.cast_sub htk, one_sub_div h2x.ne', sub_div' _ (2 : ℝ), div_sub',
      div_div_div_cancel_right, mul_one, two_mul, sub_sub, add_sub_add_right_eq_sub, add_sub_assoc]
    · positivity
    · positivity
    · positivity
  have h₃ : (↑(k - t) : ℝ) / (↑k + ↑(k - t)) ≤ 1 / 5 :=
    by
    rw [h₂, sub_le_comm, le_one_div _ h2x, sub_le_comm]
    · exact hxl.trans' (by norm_num1)
    · norm_num1
  have h₄ : (1 : ℝ) / 101 ≤ (↑(k - t) : ℝ) / (↑k + ↑(k - t)) :=
    by
    rw [h₂, le_sub_comm, one_div_le h2x, le_sub_comm]
    · exact hxu.trans (by norm_num1)
    norm_num1
  specialize hk (k - t) h₁ k _ _ rfl h₄ h₃ rfl
  rcases eq_or_ne (red_steps (2 / 5) k k (get_ini k)).card k with (htk | htk')
  · have : ((red_steps (2 / 5) k k (get_ini k)).card : ℝ) / k = 1 :=
      by
      rw [htk, div_self]
      positivity
    rw [this] at hxu 
    norm_num1 at hxu 
  have : 0 < k - t := Nat.sub_pos_of_lt (lt_of_le_of_ne htk htk')
  have h₅ : (0 : ℝ) < ramsey_number ![k, k - t] :=
    by
    rw [Nat.cast_pos, ramsey_number_pos, Fin.forall_fin_two]
    exact ⟨hk₀.ne', this.ne'⟩
  have h₆ : 1 - 1 / (2 - x) = (1 - x) / (2 - x) :=
    by
    rw [one_sub_div h2x.ne', sub_sub, add_comm, ← sub_sub]
    norm_num1
    rfl
  refine' (logb_le_logb_of_le one_le_two h₅ hk).trans _
  have h₇ : (0 : ℝ) < (k + (k - t)).choose k :=
    by
    rw [Nat.cast_pos]
    exact Nat.choose_pos le_self_add
  rw [← Nat.choose_symm_add, logb_mul (exp_pos _).ne' h₇.ne', logb, log_exp]
  refine' (add_le_add_left (F_le_f1_aux rfl hk₀ (hxu.trans (by norm_num1))) _).trans _
  rwa [mul_add, mul_sub, sub_add, neg_mul, sub_eq_add_neg (k * _ : ℝ), add_comm,
    add_le_add_iff_left, h₂, h₆, neg_add_eq_sub, sub_div, ← div_mul_eq_mul_div, div_div _ (40 : ℝ),
    neg_sub, mul_comm (k : ℝ), mul_comm (k : ℝ), mul_comm (1 / _ : ℝ), ← div_eq_mul_one_div,
    mul_comm (40 : ℝ), sub_le_sub_iff_right, ← div_le_iff' hη, ← Nat.ceil_le]

theorem eleven_one_large_end {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 0.75)
    (hx' : 0.99 ≤ x) : (2 - x) * binEnt 2 (1 / (2 - x)) + (y + x) ≤ 39 / 20 :=
  by
  rcases hx with ⟨hx₀, hx₁⟩
  suffices (2 - x) * binEnt 2 (1 / (2 - x)) ≤ 0.2 by linarith only [this, hx₁, hy.2]
  have : x ≤ 1 / (2 - x) := by
    rw [le_div_iff]
    · nlinarith
    linarith only [hx₁]
  have hb := (strict_anti_on_bin_ent_half_one one_lt_two).AntitoneOn
  rw [antitone_on_Icc_iff] at hb 
  have : (2 - x) * binEnt 2 (1 / (2 - x)) ≤ 2 * binEnt 2 x :=
    by
    have h : 1 / (2 - x) ≤ 1 := by rw [div_le_one] <;> linarith
    refine'
      mul_le_mul (by linarith [hx₀]) _ (binEnt_nonneg one_lt_two (hx₀.trans this) h) two_pos.le
    exact hb _ _ (hx'.trans' (by norm_num1)) ‹_› h
  refine' this.trans _
  rw [← le_div_iff' (zero_lt_two' ℝ)]
  refine' (bin_ent_hundredth.trans_eq (by norm_num)).trans' _
  rw [← @binEnt_symm _ (1 / 100)]
  refine' hb _ _ (by norm_num1) _ hx₁
  exact hx'.trans' (by norm_num1)

theorem eleven_one (η : ℝ) (hη : 0 < η) :
    ∀ᶠ k in atTop,
      ∃ x ∈ Set.Icc (0 : ℝ) 1,
        ∃ y ∈ Set.Icc (0 : ℝ) 0.75,
          logb 2 (ramseyNumber ![k, k]) / k ≤ max (min (f x y) (g x y)) 1.95 + η :=
  by
  have hμ₀ : (0 : ℝ) < 2 / 5 := by norm_num1
  have hμ₁ : (2 / 5 : ℝ) < 1 := by norm_num1
  obtain ⟨f₁, hf₁, hf₁'⟩ := eleven_two_improve _ hμ₀ hμ₁
  obtain ⟨f₂, hf₂, hf₂'⟩ := eleven_three_special _ hμ₀ hμ₁
  filter_upwards [hf₁', hf₂', (hf₁.add (@is_o_const_thing 1)).bound hη,
    (hf₂.add (@is_o_const_thing 1)).bound (half_pos hη), eventually_ge_at_top 4, y_le_3_4, x_le_1,
    eleven_one_special (η / 2) (half_pos hη)] with k hf₁ hf₂ hη₁ hη₂ hk₆ hy₃₄ hx₁ h₁₁
  set t := (red_steps (2 / 5) k k (get_ini k)).card
  set s := (density_steps (2 / 5) k k (get_ini k)).card
  set R := ramsey_number ![k, k]
  clear hf₁' hf₂'
  specialize hy₃₄ _ (two_le_n_of_large_k hk₆) _ (get_χ_ramsey hk₆) _ (get_ini_p' hk₆)
  specialize hx₁ _ (two_le_n_of_large_k hk₆) _ (get_χ_ramsey hk₆) _ (get_ini_p' hk₆)
  replace hf₁ : logb 2 R - 1 ≤ k * G (2 / 5) (t / k) (s / k) + _ :=
    (R_k_close_to_n k hk₆).trans
      (hf₁ _ (two_le_n_of_large_k hk₆) _ (get_χ_ramsey hk₆) _ (get_ini_p' hk₆) (get_ini_card_X hk₆))
  replace hf₂ : logb 2 R - 1 ≤ logb 2 (ramsey_number ![_, k - t]) + s + t + _ :=
    (R_k_close_to_n k hk₆).trans
      (hf₂ _ (two_le_n_of_large_k hk₆) _ (get_χ_ramsey hk₆) _ (get_ini_p' hk₆) (get_ini_card_Y hk₆))
  rw [sub_le_iff_le_add] at hf₁ hf₂ 
  specialize h₁₁ hx₁.1
  have hk₀ : 0 < k := hk₆.trans_lt' (by norm_num1)
  have hx : (t : ℝ) / k ∈ Set.Icc (0 : ℝ) 1 := ⟨by positivity, hx₁.2⟩
  have hy : (s : ℝ) / k ∈ Set.Icc (0 : ℝ) 0.75 := ⟨by positivity, hy₃₄⟩
  have hk₀' : (0 : ℝ) < k := Nat.cast_pos.2 hk₀
  rw [← g] at hf₁ 
  refine' ⟨_, hx, _, hy, _⟩
  rw [← sub_le_iff_le_add, max_min_distrib_right]
  have h₁ : f₁ k + 1 ≤ k * η :=
    by
    rw [norm_coe_nat, norm_eq_abs, mul_comm] at hη₁ 
    exact (le_abs_self _).trans hη₁
  have h₂ : (f₂ k + 1) / k ≤ η / 2 :=
    by
    rw [norm_coe_nat, norm_eq_abs, abs_le, ← div_le_iff hk₀'] at hη₂ 
    exact hη₂.2
  refine' le_min _ _
  swap
  · refine' le_max_of_le_left _
    rw [sub_le_iff_le_add, div_le_iff' hk₀']
    refine' hf₁.trans _
    rw [mul_add, add_assoc, add_le_add_iff_left]
    exact h₁
  -- f₁ k + 1 ≤ k * η
  rw [sub_le_iff_le_add]
  refine' (div_le_div_of_le hk₀'.le hf₂).trans _
  rw [← max_add_add_right]
  cases' lt_or_le 0.99 ((t : ℝ) / k) with hx99 hx99
  · refine' le_max_of_le_right _
    rw [add_assoc, add_div, add_assoc]
    refine' add_le_add _ (h₂.trans (half_le_self hη.le))
    -- (f₂ k + 1) / k ≤ η
    rw [add_div, add_div]
    refine' (add_le_add_right (div_le_div_of_le hk₀'.le (F_le_f1 rfl hk₀ hx.2)) _).trans _
    rw [mul_div_cancel_left _ hk₀'.ne']
    exact eleven_one_large_end hx hy hx99.le
  refine' le_max_of_le_left _
  cases' lt_or_le ((t : ℝ) / k) 0.75 with hx34 hx34
  · rw [f, if_neg hx34.not_le, f1, add_assoc, add_div, add_div, add_div]
    refine' add_le_add _ (h₂.trans (half_le_self hη.le))
    rw [add_right_comm, add_rotate, add_le_add_iff_left, div_le_iff' hk₀']
    exact F_le_f1 rfl hk₀ hx.2
  rw [f, if_pos hx34, f2, add_assoc, add_div, add_div, add_div, add_assoc, add_assoc]
  refine' (add_le_add_right (div_le_div_of_le hk₀'.le (h₁₁ hx34 hx99)) _).trans _
  rw [mul_div_cancel_left _ hk₀'.ne', add_sub_assoc, add_assoc, add_right_comm, add_comm,
    add_le_add_iff_right, add_assoc, add_left_comm, add_left_comm (t / k : ℝ), add_le_add_iff_left,
    add_left_comm, add_le_add_iff_left]
  have : (f₂ k + 1) / k ≤ η / 2 := h₂
  exact (add_le_add_left this _).trans_eq (add_halves _)

end SimpleGraph

