/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ExponentialRamsey.Section5

/-!
# Section 6
-/

namespace SimpleGraph

open scoped BigOperators ExponentialRamsey

open Filter Finset Real

variable {V : Type*} [DecidableEq V] [Fintype V] {χ : TopEdgeLabelling V (Fin 2)}

variable {k l : ℕ} {ini : BookConfig χ} {i : ℕ}

set_option hygiene false in
local notation:max "p_" i:max => (algorithm μ k l ini i).p

set_option hygiene false in
local notation "ℛ" => redSteps μ k l ini

set_option hygiene false in
local notation "ℬ" => bigBlueSteps μ k l ini

set_option hygiene false in
local notation "𝒮" => densitySteps μ k l ini

set_option hygiene false in
local notation "𝒟" => degreeSteps μ k l ini

set_option hygiene false in
local notation "ε" => (k : ℝ) ^ (-1 / 4 : ℝ)

theorem six_four_red {μ : ℝ} (hi : i ∈ redSteps μ k l ini) :
    (algorithm μ k l ini i).p - αFunction k (height k ini.p (algorithm μ k l ini i).p) ≤
      (algorithm μ k l ini (i + 1)).p := by
  change (_ : ℝ) ≤ red_density χ _ _
  rw [red_applied hi, BookConfig.redStepBasic_x, BookConfig.redStepBasic_Y]
  have hi' := hi
  simp only [redSteps, mem_image, mem_filter, mem_attach, true_and,
    Subtype.exists, exists_and_right, exists_eq_right] at hi'
  obtain ⟨hx, hx'⟩ := hi'
  exact hx'

theorem six_four_density (μ₁ p₀l : ℝ) (hμ₁ : μ₁ < 1) (hp₀l : 0 < p₀l) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ,
            μ ≤ μ₁ →
              ∀ n : ℕ,
                ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                  ∀ ini : BookConfig χ,
                    p₀l ≤ ini.p →
                      ∀ i : ℕ,
                        i ∈ densitySteps μ k l ini →
                          (algorithm μ k l ini i).p ≤ (algorithm μ k l ini (i + 1)).p :=
  five_three_left _ _ hμ₁ hp₀l

theorem six_four_density' (μ₁ p₀ : ℝ) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ,
            μ ≤ μ₁ →
              ∀ n,
                ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                  ∀ ini : BookConfig χ, p₀ ≤ ini.p → ∀ i : ℕ, i ∈ 𝒮 → p_ i ≤ p_ (i + 1) :=
  six_four_density μ₁ p₀ hμ₁ hp₀

theorem increase_average {α : Type*} {s : Finset α} {f : α → ℝ} {k : ℝ}
    (hk : k ≤ (∑ i ∈ s, f i) / s.card) :
    (∑ i ∈ s, f i) / s.card ≤
      (∑ i ∈ (s.filter fun j => k ≤ f j), f i) / (s.filter fun j => k ≤ f j).card := by
  classical
  rcases s.eq_empty_or_nonempty with (rfl | hs)
  · rw [filter_empty]
  have hs' : (0 : ℝ) < s.card := by rwa [Nat.cast_pos, card_pos]
  have : (s.filter fun j => k ≤ f j).Nonempty := by
    rw [nonempty_iff_ne_empty, ne_eq, filter_eq_empty_iff]
    intro h
    simp only [not_le] at h
    rw [le_div_iff₀' hs'] at hk
    refine' (sum_lt_sum_of_nonempty hs h).not_ge _
    rwa [sum_const, nsmul_eq_mul]
  have hs'' : (0 : ℝ) < (s.filter fun j => k ≤ f j).card := by rwa [Nat.cast_pos, card_pos]
  rw [div_le_div_iff₀ hs' hs'', ← sum_filter_add_sum_filter_not s fun j : α => k ≤ f j,
    add_mul, ← le_sub_iff_add_le', ← mul_sub,
    ← cast_card_sdiff (filter_subset _ s), mul_comm]
  have h₁ : ∑ i ∈ s.filter fun x => ¬k ≤ f x, f i ≤ (s.filter fun x => ¬k ≤ f x).card * k := by
    rw [← nsmul_eq_mul]
    refine' sum_le_card_nsmul _ _ _ _
    simp (config := { contextual := true }) [le_of_lt]
  have h₂ : ((s.filter fun x => k ≤ f x).card : ℝ) * k ≤ ∑ i ∈ s.filter fun j => k ≤ f j, f i := by
    rw [← nsmul_eq_mul]
    refine' card_nsmul_le_sum _ _ _ _
    simp (config := { contextual := true })
  refine' (mul_le_mul_of_nonneg_left h₁ (Nat.cast_nonneg _)).trans _
  refine' (mul_le_mul_of_nonneg_right h₂ (Nat.cast_nonneg _)).trans' _
  rw [← filter_not, mul_right_comm, mul_assoc]

theorem colDensity_eq_average {i : Fin 2} {X Y : Finset V} :
    colDensity χ i X Y = (∑ x ∈ X, ((colNeighbors χ i x ∩ Y).card : ℝ) / Y.card) / X.card := by
  rw [colDensity_eq_sum, ← sum_div, div_div, mul_comm, Nat.cast_sum]

theorem six_four_degree {μ : ℝ} (hi : i ∈ degreeSteps μ k l ini) : p_ i ≤ p_ (i + 1) := by
  change red_density χ _ _ ≤ red_density χ _ _
  rw [degree_regularisation_applied hi, BookConfig.degreeRegularisationStep_x,
    BookConfig.degreeRegularisationStep_Y]
  set C := algorithm μ k l ini i
  set α := αFunction k (height k ini.p C.p)
  rw [colDensity_eq_average]
  have :
    (C.X.filter fun x =>
        (C.p - k ^ (1 / 8 : ℝ) * α) * C.Y.card ≤ (colNeighbors χ 0 x ∩ C.Y).card) =
      C.X.filter fun x =>
        C.p - k ^ (1 / 8 : ℝ) * α ≤
          (colNeighbors χ 0 x ∩ C.Y).card / C.Y.card := by
    refine' filter_congr _
    intro x hx
    rw [le_div_iff₀]
    rw [Nat.cast_pos, card_pos]
    refine' Y_nonempty _
    rw [degreeSteps, mem_filter, mem_range] at hi
    exact hi.1
  rw [this, colDensity_eq_average]
  refine' increase_average _
  rw [← colDensity_eq_average, BookConfig.p, sub_le_self_iff]
  exact mul_nonneg (rpow_nonneg (Nat.cast_nonneg _) _) (α_nonneg _ _)

theorem BookConfig.getBook_snd_nonempty {V : Type*} [DecidableEq V] {χ} {μ : ℝ} (hμ₀ : 0 < μ)
    {X : Finset V} (hX : X.Nonempty) : (BookConfig.getBook χ μ X).2.Nonempty := by
  rw [← card_pos, ← @Nat.cast_pos ℝ]
  refine' BookConfig.getBook_relative_card.trans_lt' _
  refine' div_pos (mul_pos (pow_pos hμ₀ _) _) two_pos
  rwa [Nat.cast_pos, card_pos]

theorem six_four_blue' {μ : ℝ} (hμ₀ : 0 < μ) (hi : i + 1 ∈ bigBlueSteps μ k l ini) :
    p_ i - k ^ (1 / 8 : ℝ) * αFunction k (height k ini.p (p_ i)) ≤ p_ (i + 2) := by
  change _ ≤ red_density χ _ _
  rw [big_blue_applied hi, BookConfig.bigBlueStep_x, BookConfig.bigBlueStep_Y]
  have h : i + 1 < finalStep μ k l ini := by
    rw [bigBlueSteps, mem_filter, mem_range] at hi
    exact hi.1
  have hi' : i ∈ degreeSteps μ k l ini := by
    rw [bigBlueSteps, mem_filter, Nat.even_add_one, Classical.not_not] at hi
    rw [degreeSteps, mem_filter, mem_range]
    exact ⟨h.trans_le' (Nat.le_succ _), hi.2.1⟩
  rw [degree_regularisation_applied hi', BookConfig.degreeRegularisationStep_Y, ←
    degree_regularisation_applied hi']
  rw [colDensity_eq_average]
  let C := algorithm μ k l ini i
  let C' := algorithm μ k l ini (i + 1)
  have :
    ∀ x ∈ (C'.bigBlueStep μ).X,
      C.p - k ^ (1 / 8 : ℝ) * αFunction k (height k ini.p C.p) ≤
        (red_neighbors χ x ∩ C.Y).card / C.Y.card := by
    intro x hx
    have : x ∈ (algorithm μ k l ini (i + 1)).X := BookConfig.getBook_snd_subset hx
    rw [degree_regularisation_applied hi', BookConfig.degreeRegularisationStep_x,
      mem_filter] at this
    rw [le_div_iff₀]
    · exact this.2
    rw [Nat.cast_pos, card_pos]
    refine' Y_nonempty _
    exact h.trans_le' (Nat.le_succ _)
  refine' (div_le_div_of_nonneg_right (card_nsmul_le_sum _ _ _ this) (Nat.cast_nonneg _)).trans' _
  rw [BookConfig.bigBlueStep_x, nsmul_eq_mul, mul_div_cancel_left₀]
  rw [Nat.cast_ne_zero, ← pos_iff_ne_zero, card_pos]
  refine' BookConfig.getBook_snd_nonempty hμ₀ _
  exact x_nonempty h

theorem six_four_blue {μ : ℝ} (hμ₀ : 0 < μ) (hi : i ∈ bigBlueSteps μ k l ini) :
    (algorithm μ k l ini (i - 1)).p -
        k ^ (1 / 8 : ℝ) * αFunction k (height k ini.p (algorithm μ k l ini (i - 1)).p) ≤
      (algorithm μ k l ini (i + 1)).p := by
  have hi' := hi
  rw [bigBlueSteps, mem_filter, Nat.not_even_iff_odd] at hi
  obtain ⟨b, rfl⟩ := hi.2.1.exists_bit1
  refine' six_four_blue' hμ₀ _
  rw [Nat.add_sub_cancel]
  exact hi'

theorem height_mono {p₀ p₁ p₂ : ℝ} (hk : k ≠ 0) (h : p₁ ≤ p₂) :
    height k p₀ p₁ ≤ height k p₀ p₂ := by
  refine' height_min hk _ _
  · rw [← pos_iff_ne_zero]
    exact one_le_height
  exact h.trans (height_spec hk)

theorem six_five_density (μ₁ p₀l : ℝ) (hμ₁ : μ₁ < 1) (hp₀l : 0 < p₀l) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ,
            μ ≤ μ₁ →
              ∀ n : ℕ,
                ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                  ∀ ini : BookConfig χ,
                    p₀l ≤ ini.p →
                      ∀ i : ℕ,
                        i ∈ densitySteps μ k l ini →
                          height k ini.p (algorithm μ k l ini i).p ≤
                            height k ini.p (algorithm μ k l ini (i + 1)).p := by
  filter_upwards [six_four_density μ₁ p₀l hμ₁ hp₀l, top_adjuster (eventually_ne_atTop 0)] with l hl
    hk' k hlk μ hμu n χ ini hini i hi
  exact height_mono (hk' _ hlk) (hl k hlk μ hμu n χ ini hini i hi)

theorem six_five_degree :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ,
            ∀ n : ℕ,
              ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                ∀ ini : BookConfig χ,
                  ∀ i : ℕ,
                    i ∈ degreeSteps μ k l ini →
                      height k ini.p (algorithm μ k l ini i).p ≤
                        height k ini.p (algorithm μ k l ini (i + 1)).p := by
  filter_upwards [top_adjuster (eventually_ne_atTop 0)] with l hk' k hlk μ n χ ini i hi
  exact height_mono (hk' _ hlk) (six_four_degree hi)

open scoped Topology

theorem six_five_red_aux : ∀ᶠ x : ℝ in 𝓝[≥] 0, x * (1 + x) ^ 2 + 1 ≤ (1 + x) ^ 2 := by
  rw [eventually_nhdsWithin_iff]
  filter_upwards [eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2)] with x hx₂ hx₀
  rw [Set.mem_Ici] at hx₀
  rw [← sub_nonpos]
  ring_nf
  nlinarith

theorem six_five_red_aux_glue :
    ∀ᶠ k : ℕ in atTop,
      (k : ℝ) ^ (-(1 / 4) : ℝ) * (1 + k ^ (-(1 / 4) : ℝ)) ^ 2 + 1 ≤
        (1 + (k : ℝ) ^ (-(1 / 4) : ℝ)) ^ 2 := by
  suffices Tendsto (fun k : ℕ => (k : ℝ) ^ (-(1 / 4) : ℝ)) atTop (𝓝[≥] 0) by
    exact this.eventually six_five_red_aux
  rw [tendsto_nhdsWithin_iff]
  refine' ⟨(tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop, _⟩
  refine' Filter.Eventually.of_forall _
  intro x
  exact rpow_nonneg (Nat.cast_nonneg _) _

theorem Nat.cast_sub_le {x y : ℕ} : (x - y : ℝ) ≤ (x - y : ℕ) := by
  rw [sub_le_iff_le_add, ← Nat.cast_add, Nat.cast_le, ← tsub_le_iff_right]

theorem six_five_red :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ,
            ∀ n : ℕ,
              ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                ∀ ini : BookConfig χ,
                  ∀ i : ℕ,
                    i ∈ redSteps μ k l ini →
                      height k ini.p (algorithm μ k l ini i).p - 2 ≤
                        height k ini.p (algorithm μ k l ini (i + 1)).p := by
  filter_upwards [top_adjuster (eventually_ne_atTop 0), top_adjuster six_five_red_aux_glue] with l
    hk' hk'' k hlk μ n χ ini i hi
  set p := (algorithm μ k l ini i).p
  set h := height k ini.p p
  specialize hk' k hlk
  cases' lt_or_ge h 4 with hh hh
  · rw [Nat.lt_succ_iff] at hh
    rw [tsub_le_iff_right]
    refine' hh.trans _
    rw [Nat.succ_le_succ_iff, Nat.succ_le_succ_iff]
    exact one_le_height
  suffices ht : qFunction k ini.p (h - 3) < (algorithm μ k l ini (i + 1)).p
  · by_contra! ht'
    rw [lt_tsub_iff_right, Nat.lt_iff_add_one_le, add_assoc, ← le_tsub_iff_right] at ht'
    swap
    · exact hh.trans' (Nat.le_succ _)
    have := (q_increasing ht').trans_lt ht
    exact this.not_ge (height_spec hk')
  refine' (six_four_red hi).trans_lt' _
  have : qFunction k ini.p (h - 1) < p := q_height_lt_p (hh.trans_lt' (by norm_num))
  refine' (sub_lt_sub_right this _).trans_le' _
  change qFunction _ _ _ ≤ _ - αFunction _ h
  rw [qFunction, qFunction, add_sub_assoc, add_le_add_iff_left, αFunction, ← sub_div]
  refine' div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [le_sub_iff_add_le', add_sub_assoc', sub_le_sub_iff_right, neg_div]
  have : h - 1 = h - 3 + 2 := by
    rw [Nat.sub_eq_iff_eq_add, add_assoc, Nat.sub_add_cancel]
    · exact hh.trans' (Nat.le_succ _)
    · exact hh.trans' (by norm_num)
  rw [this, add_comm _ 2, pow_add, ← mul_assoc, ← add_one_mul]
  refine' mul_le_mul_of_nonneg_right _ (pow_nonneg (by positivity) _)
  exact hk'' k hlk

theorem convex_thing_aux {x : ℝ} (hε : 0 ≤ x) (hx' : x ≤ 2 / 7) :
    exp (-(7 * log 2 / 4 * x)) ≤ 1 - 7 / 2 * (1 - 1 / sqrt 2) * x := by
  have h' : (0 : ℝ) < log 2 := log_pos (by norm_num)
  let a := -log 2 / 2
  have : -log 2 / 2 ≠ 0 := by norm_num
  refine' (general_convex_thing' _ _ this).trans_eq _
  · rw [neg_nonpos]
    positivity
  · nlinarith
  have : exp (-log 2 / 2) = 1 / sqrt 2 := by
    rw [div_eq_mul_one_div, neg_mul, Real.exp_neg, exp_mul, exp_log, rpow_div_two_eq_sqrt, rpow_one,
        one_div] <;>
      norm_num
  rw [this, neg_div, mul_div_assoc, neg_div, ← div_neg, neg_neg, div_div_eq_mul_div,
    sub_eq_add_neg _ (_ * _ : ℝ), add_right_inj, div_mul_eq_mul_div, div_mul_eq_mul_div, div_div,
    mul_right_comm _ (log 2), mul_right_comm _ (log 2), mul_div_mul_right _ _ h'.ne', ← neg_mul, ←
    mul_neg, neg_sub, mul_right_comm (7 / 2 : ℝ), mul_comm, mul_right_comm (7 : ℝ), ←
    div_mul_eq_mul_div]
  congr 2
  norm_num1

theorem convex_thing {x : ℝ} (hε : 0 ≤ x) (hε' : x ≤ 2 / 7) :
    exp (-(7 * log 2 / 4 * x)) ≤ 1 - x := by
  refine' (convex_thing_aux hε hε').trans _
  rw [sub_le_sub_iff_left]
  refine' le_mul_of_one_le_left hε _
  rw [← div_le_iff₀', le_sub_comm, one_div]
  swap
  · norm_num1
  refine' inv_le_of_inv_le₀ (by norm_num) _
  refine' le_sqrt_of_sq_le _
  norm_num

theorem six_five_blue_aux : ∀ᶠ x : ℝ in 𝓝 0, 0 < x → (1 + x ^ 2) ^ (-⌊2 * x⁻¹⌋₊ : ℝ) ≤ 1 - x := by
  have h₁ := (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).const_mul_atTop
    (by norm_num : (0 : ℝ) < 2)
  have h₂ := h₁.eventually (eventually_le_floor (7 / 8) (by norm_num))
  rw [eventually_nhdsWithin_iff] at h₂
  filter_upwards [h₂, eventually_lt_nhds (by norm_num : (0 : ℝ) < 1),
    eventually_le_nhds (by norm_num : (0 : ℝ) < 2 / 7)] with x hε hε₁ hε₂₇ hε₀
  specialize hε hε₀
  have : 7 / (4 * x) ≤ ⌊2 * x⁻¹⌋₊ := by
    refine' hε.trans_eq' _
    rw [← div_div, div_eq_mul_inv, ← mul_assoc, div_eq_mul_inv]
    norm_num
  have h₃ : 1 < 1 + x ^ 2 := by
    rw [lt_add_iff_pos_right]
    exact pow_pos hε₀ _
  have h₄ : 0 < 1 + x ^ 2 := zero_lt_one.trans h₃
  rw [← log_le_log_iff (rpow_pos_of_pos h₄ _) (sub_pos_of_lt hε₁), log_rpow h₄, neg_mul, neg_le]
  refine'
    (mul_le_mul this (mul_log_two_le_log_one_add (pow_nonneg hε₀.le _) _)
          (mul_nonneg (pow_nonneg hε₀.le _) (log_nonneg one_lt_two.le)) (Nat.cast_nonneg _)).trans'
      _
  · exact pow_le_one₀ hε₀.le hε₁.le
  have : 7 / (4 * x) * (x ^ 2 * log 2) = 7 * log 2 / 4 * x := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← mul_assoc, mul_right_comm, sq, ← mul_assoc,
      mul_div_mul_right _ _ hε₀.ne']
  rw [this, neg_le, le_log_iff_exp_le (sub_pos_of_lt hε₁)]
  exact convex_thing hε₀.le hε₂₇

theorem six_five_blue (μ₀ : ℝ) (hμ₀ : 0 < μ₀) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ,
            μ₀ ≤ μ →
              ∀ n : ℕ,
                ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                  ∀ ini : BookConfig χ,
                    ∀ i : ℕ,
                      i ∈ bigBlueSteps μ k l ini →
                        (height k ini.p (algorithm μ k l ini (i - 1)).p : ℝ) -
                            2 * (k : ℝ) ^ (1 / 8 : ℝ) ≤
                          height k ini.p (algorithm μ k l ini (i + 1)).p := by
  have : Tendsto (fun k : ℕ => (k : ℝ) ^ (-(1 / 8) : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [top_adjuster (eventually_gt_atTop 0),
    top_adjuster (this.eventually six_five_blue_aux)] with l hk₀ hkε k hlk μ hμl n χ ini i hi
  specialize hk₀ k hlk
  set p := (algorithm μ k l ini (i - 1)).p
  set h := height k ini.p p
  have hk : (0 : ℝ) ≤ k ^ (1 / 8 : ℝ) := rpow_nonneg (Nat.cast_nonneg _) _
  have hk' : (0 : ℝ) ≤ 2 * k ^ (1 / 8 : ℝ) := mul_nonneg two_pos.le hk
  cases' le_or_gt ((h : ℝ) - 2 * k ^ (1 / 8 : ℝ)) 1 with hh hh
  · refine' hh.trans _
    rw [Nat.one_le_cast]
    exact one_le_height
  have : qFunction k ini.p (h - 1) < p := by
    refine' q_height_lt_p _
    rw [← @Nat.one_lt_cast ℝ]
    refine' hh.trans_le _
    rw [sub_le_self_iff]
    exact hk'
  change (h : ℝ) - _ ≤ _
  rw [sub_le_iff_le_add, ← Nat.le_floor_iff, add_comm, Nat.floor_add_natCast hk',
    ← tsub_le_iff_left]
  rotate_left
  · exact add_nonneg (Nat.cast_nonneg _) hk'
  have z : 1 ≤ h - ⌊2 * (k : ℝ) ^ (1 / 8 : ℝ)⌋₊ := by
    rw [Nat.succ_le_iff]
    refine' Nat.sub_pos_of_lt _
    rw [Nat.floor_lt hk', ← sub_pos]
    exact hh.trans_le' zero_le_one
  suffices ht :
    qFunction k ini.p (h - ⌊2 * (k : ℝ) ^ (1 / 8 : ℝ)⌋₊ - 1) < (algorithm μ k l ini (i + 1)).p
  · by_contra! ht'
    rw [Nat.lt_iff_add_one_le, ← le_tsub_iff_right z] at ht'
    have := (q_increasing ht').trans_lt ht
    exact this.not_ge (height_spec hk₀.ne')
  refine' (six_four_blue (hμ₀.trans_le hμl) hi).trans_lt' _
  refine' (sub_lt_sub_right this _).trans_le' _
  rw [αFunction, qFunction, qFunction, add_sub_assoc, add_le_add_iff_left, mul_div_assoc', ←
    sub_div]
  refine' div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hz : (0 : ℝ) < 1 + ε :=
    add_pos_of_pos_of_nonneg zero_lt_one (rpow_nonneg (Nat.cast_nonneg _) _)
  rw [sub_sub, add_comm (1 : ℝ) (_ * _), ← sub_sub, sub_le_sub_iff_right, ← mul_assoc, ←
    one_sub_mul, tsub_tsub, add_comm _ 1, ← tsub_tsub, pow_sub₀, mul_comm]
  rotate_left
  · exact hz.ne'
  · rw [← @Nat.cast_le ℝ]
    refine' (Nat.floor_le hk').trans _
    refine' Nat.cast_sub_le.trans' _
    grind
  refine' mul_le_mul_of_nonneg_right _ (pow_nonneg hz.le _)
  let ν : ℝ := k ^ (-(1 / 8) : ℝ)
  suffices (1 + ν ^ 2) ^ (-⌊2 * ν⁻¹⌋₊ : ℝ) ≤ 1 - ν by
    convert (config := { sameFun := true }) this using 2
    · rw [← rpow_natCast, ← rpow_neg hz.le, ← rpow_neg (Nat.cast_nonneg _), neg_neg, ← rpow_two, ←
        rpow_mul (Nat.cast_nonneg _)]
      norm_num
    rw [← rpow_add' (Nat.cast_nonneg _)]
    · congr 1
      norm_num1
    norm_num1
  exact hkε k hlk (rpow_pos_of_pos (Nat.cast_pos.2 hk₀) _)

/-- the set of steps on which p is below p₀ and decreases in two steps -/
noncomputable def decreaseSteps (μ : ℝ) (k l : ℕ) (ini : BookConfig χ) : Finset ℕ :=
  (redSteps μ k l ini ∪ bigBlueSteps μ k l ini ∪ densitySteps μ k l ini).filter fun i =>
    (algorithm μ k l ini (i + 1)).p < (algorithm μ k l ini (i - 1)).p ∧
      (algorithm μ k l ini (i - 1)).p ≤ ini.p

theorem sub_one_mem_degree {μ : ℝ} {i : ℕ} (hi : i < finalStep μ k l ini) (hi' : Odd i) :
    1 ≤ i ∧ i - 1 ∈ degreeSteps μ k l ini := by
  obtain ⟨i, rfl⟩ := hi'.exists_bit1
  refine' ⟨by simp, _⟩
  rw [Nat.add_sub_cancel, degreeSteps, mem_filter, mem_range]
  exact ⟨hi.trans_le' (Nat.le_succ _), even_two_mul _⟩

theorem bigBlueSteps_sub_one_mem_degree {μ : ℝ} {i : ℕ} (hi : i ∈ bigBlueSteps μ k l ini) :
    1 ≤ i ∧ i - 1 ∈ degreeSteps μ k l ini := by
  rw [bigBlueSteps, mem_filter, mem_range, Nat.not_even_iff_odd] at hi
  exact sub_one_mem_degree hi.1 hi.2.1

theorem redOrDensitySteps_sub_one_mem_degree {μ : ℝ} {i : ℕ}
    (hi : i ∈ redOrDensitySteps μ k l ini) : 1 ≤ i ∧ i - 1 ∈ degreeSteps μ k l ini := by
  rw [redOrDensitySteps, mem_filter, mem_range, Nat.not_even_iff_odd] at hi
  exact sub_one_mem_degree hi.1 hi.2.1

theorem redSteps_sub_one_mem_degree {μ : ℝ} {i : ℕ} (hi : i ∈ redSteps μ k l ini) :
    1 ≤ i ∧ i - 1 ∈ degreeSteps μ k l ini :=
  redOrDensitySteps_sub_one_mem_degree (redSteps_subset_redOrDensitySteps hi)

theorem densitySteps_sub_one_mem_degree {μ : ℝ} {i : ℕ} (hi : i ∈ densitySteps μ k l ini) :
    1 ≤ i ∧ i - 1 ∈ degreeSteps μ k l ini :=
  redOrDensitySteps_sub_one_mem_degree (densitySteps_subset_redOrDensitySteps hi)

theorem height_eq_one {p₀ p : ℝ} (h : p ≤ p₀) : height k p₀ p = 1 := by
  apply five_seven_extra
  rw [qFunction, pow_one, add_sub_cancel_left]
  refine' h.trans _
  simp only [le_add_iff_nonneg_right]
  positivity

theorem six_three_blue (μ₀ : ℝ) (hμ₀ : 0 < μ₀) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ,
            μ₀ ≤ μ →
              ∀ n : ℕ,
                ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                  (¬∃ (m : Finset (Fin n)) (c : Fin 2),
                        χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                    ∀ ini : BookConfig χ,
                      ∑ i ∈
                          ((bigBlueSteps μ k l ini).filter fun i =>
                            (algorithm μ k l ini (i + 1)).p < (algorithm μ k l ini (i - 1)).p ∧
                              (algorithm μ k l ini (i - 1)).p ≤ ini.p),
                          ((algorithm μ k l ini (i - 1)).p - (algorithm μ k l ini (i + 1)).p) ≤
                        ε := by
  filter_upwards [top_adjuster (eventually_ge_atTop 1), four_three hμ₀] with l hl₁ hb k hlk μ hμl n
    χ hχ ini
  let BZ :=
    (bigBlueSteps μ k l ini).filter fun i =>
      (algorithm μ k l ini (i + 1)).p < (algorithm μ k l ini (i - 1)).p ∧
        (algorithm μ k l ini (i - 1)).p ≤ ini.p
  change ∑ i ∈ BZ, _ ≤ _
  have : ∀ i ∈ BZ, (algorithm μ k l ini (i - 1)).p - (algorithm μ k l ini (i + 1)).p ≤ 1 / k := by
    intro i hi
    rw [mem_filter] at hi
    have : height k ini.p (algorithm μ k l ini (i - 1)).p = 1 := by
      refine' height_eq_one _
      exact hi.2.2
    have h' := six_four_blue (hμ₀.trans_le hμl) hi.1
    rw [this, sub_le_comm] at h'
    refine' h'.trans _
    rw [α_one, mul_div_assoc']
    refine' div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    rw [← rpow_add' (Nat.cast_nonneg _)]
    refine' rpow_le_one_of_one_le_of_nonpos (Nat.one_le_cast.2 (hl₁ k hlk)) (by norm_num)
    norm_num
  refine' (sum_le_card_nsmul _ _ _ this).trans _
  rw [nsmul_eq_mul, mul_one_div]
  have : (BZ.card : ℝ) ≤ l ^ (3 / 4 : ℝ) := by
    refine' (hb k hlk μ hμl n χ hχ ini).trans' _
    rw [Nat.cast_le]
    exact card_le_card (filter_subset _ _)
  refine' (div_le_div_of_nonneg_right this (Nat.cast_nonneg _)).trans _
  have : (0 : ℝ) < k := by
    rw [Nat.cast_pos]
    exact hl₁ k hlk
  rw [div_le_iff₀ this, ← rpow_add_one this.ne']
  exact (rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.2 hlk) (by norm_num)).trans_eq (by norm_num)

theorem p₀_lt_of_one_lt_height {k : ℕ} {p₀ p : ℝ} (h : 1 < height k p₀ p) : p₀ < p := by
  by_contra!
  rw [height_eq_one this] at h
  simp at h

theorem six_three_red_aux :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ,
            ∀ n : ℕ,
              ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                ∀ ini : BookConfig χ,
                  ∀ i ∈ redSteps μ k l ini,
                    (algorithm μ k l ini (i + 1)).p < (algorithm μ k l ini (i - 1)).p →
                      (algorithm μ k l ini (i - 1)).p ≤ ini.p →
                        (algorithm μ k l ini (i - 1)).p - (algorithm μ k l ini (i + 1)).p ≤
                          ε / k := by
  filter_upwards [top_adjuster (eventually_ge_atTop 1)] with l hl₁ k hlk μ n χ ini i hi hi₁ hi₂
  refine' (sub_le_sub_left (six_four_red hi) _).trans _
  cases' eq_or_lt_of_le one_le_height with h h
  · rw [← sub_add, ← h, α_one, add_le_iff_nonpos_left, sub_nonpos]
    have := redSteps_sub_one_mem_degree hi
    refine' (six_four_degree this.2).trans_eq _
    rw [Nat.sub_add_cancel this.1]
  have m := p₀_lt_of_one_lt_height h
  have : qFunction k ini.p 0 ≤ (algorithm μ k l ini i).p := by
    rw [qFunction_zero]
    exact m.le
  refine' (sub_le_sub_right hi₂ _).trans _
  rw [← sub_add]
  refine' (add_le_add_right (five_seven_right this) _).trans _
  rw [qFunction_zero, mul_add, mul_one_div, ← add_assoc, add_le_iff_nonpos_left, ←
    le_neg_iff_add_nonpos_left, neg_sub]
  refine' mul_le_of_le_one_left _ _
  · rw [sub_nonneg]
    exact m.le
  refine' rpow_le_one_of_one_le_of_nonpos _ (by norm_num)
  rw [Nat.one_le_cast]
  exact hl₁ k hlk

theorem six_three_red :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ,
            ∀ n : ℕ,
              ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                (¬∃ (m : Finset (Fin n)) (c : Fin 2), χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                  ∀ ini : BookConfig χ,
                    ∑ i ∈
                        ((redSteps μ k l ini).filter fun i =>
                          (algorithm μ k l ini (i + 1)).p < (algorithm μ k l ini (i - 1)).p ∧
                            (algorithm μ k l ini (i - 1)).p ≤ ini.p),
                        ((algorithm μ k l ini (i - 1)).p - (algorithm μ k l ini (i + 1)).p) ≤
                      ε := by
  filter_upwards [eventually_gt_atTop 0, six_three_red_aux] with l hl₀ hlr k hlk μ n χ hχ ini
  let RZ :=
    (redSteps μ k l ini).filter fun i =>
      (algorithm μ k l ini (i + 1)).p < (algorithm μ k l ini (i - 1)).p ∧
        (algorithm μ k l ini (i - 1)).p ≤ ini.p
  change ∑ i ∈ RZ, (_ : ℝ) ≤ _
  have : ∀ i ∈ RZ, (algorithm μ k l ini (i - 1)).p - (algorithm μ k l ini (i + 1)).p ≤ ε / k := by
    intro i hi
    simp only [RZ, mem_filter] at hi
    exact hlr k hlk μ n χ ini i hi.1 hi.2.1 hi.2.2
  refine' (sum_le_card_nsmul _ _ _ this).trans _
  have : (RZ.card : ℝ) ≤ k := by
    rw [Nat.cast_le]
    refine' (card_le_card (filter_subset _ _)).trans _
    exact four_four_red μ hχ ini
  rw [nsmul_eq_mul]
  refine' (mul_le_mul_of_nonneg_right this _).trans_eq _
  · positivity
  rw [mul_div_cancel₀]
  rw [Nat.cast_ne_zero]
  exact (hl₀.trans_le hlk).ne'

theorem six_three (μ₀ μ₁ p₀ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
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
                          ∑ i ∈ decreaseSteps μ k l ini,
                              ((algorithm μ k l ini (i - 1)).p - (algorithm μ k l ini (i + 1)).p) ≤
                            2 * ε := by
  filter_upwards [six_four_density μ₁ p₀ hμ₁ hp₀, six_three_red, six_three_blue μ₀ hμ₀] with l hld
    hlr hlb k hlk μ hμl hμu n χ hχ ini hini
  specialize hlr k hlk μ n χ hχ ini
  specialize hlb k hlk μ hμl n χ hχ ini
  have :
    ((densitySteps μ k l ini).filter fun i =>
        (algorithm μ k l ini (i + 1)).p < (algorithm μ k l ini (i - 1)).p ∧
          (algorithm μ k l ini (i - 1)).p ≤ ini.p) =
      ∅ := by
    rw [filter_eq_empty_iff]
    intro i hi
    rw [not_and_or, not_lt]
    left
    refine' (hld k hlk μ hμu n χ ini hini i hi).trans' _
    have := densitySteps_sub_one_mem_degree hi
    refine' (six_four_degree this.2).trans _
    rw [Nat.sub_add_cancel this.1]
  rw [decreaseSteps, filter_union, this, union_empty, filter_union, sum_union]
  · clear this
    refine' (add_le_add hlr hlb).trans_eq _
    rw [two_mul]
  clear this hlr hlb
  refine' disjoint_filter_filter _
  refine' bigBlueSteps_disjoint_redOrDensitySteps.symm.mono_left _
  exact redSteps_subset_redOrDensitySteps

theorem α_increasing {h₁ h₂ : ℕ} (hh : h₁ ≤ h₂) : αFunction k h₁ ≤ αFunction k h₂ := by
  refine' div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  refine' mul_le_mul_of_nonneg_left _ (rpow_nonneg (Nat.cast_nonneg _) _)
  refine' pow_le_pow_right₀ _ _
  · rw [le_add_iff_nonneg_right]
    exact rpow_nonneg (Nat.cast_nonneg _) _
  exact Nat.sub_le_sub_right hh _

theorem six_four_weak_aux :
    ∀ᶠ k : ℝ in atTop,
      ∀ h : ℕ,
        1 ≤ h →
          (1 + k ^ (-1 / 4 : ℝ)) ^ (h + 2 - 1) ≤
            k ^ (1 / 8 : ℝ) * (1 + k ^ (-1 / 4 : ℝ)) ^ (h - 1) := by
  have h₄ := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)
  have h₈ := tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)
  have := eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 4)
  filter_upwards [eventually_ge_atTop (0 : ℝ), h₄.eventually this, h₈.eventually_ge_atTop 2] with
    k hk₀ hk₄ hk₈ h hh
  rw [Nat.sub_add_comm hh, pow_add, mul_comm, neg_div]
  have : 0 ≤ 1 + k ^ (-(1 / 4 : ℝ)) :=
    le_add_of_nonneg_of_le zero_le_one (rpow_nonneg hk₀ _)
  refine' mul_le_mul_of_nonneg_right _ (pow_nonneg this _)
  refine' hk₈.trans' _
  refine' (pow_le_pow_left₀ this (add_le_add_right hk₄ (1 : ℝ)) _).trans _
  norm_num

theorem six_four_weak (μ₀ μ₁ p₀ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ,
            μ₀ ≤ μ →
              μ ≤ μ₁ →
                ∀ n : ℕ,
                  ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                    ∀ ini : BookConfig χ,
                      p₀ ≤ ini.p →
                        ∀ i : ℕ,
                          i ∈ redSteps μ k l ini ∪ bigBlueSteps μ k l ini ∪ densitySteps μ k l ini →
                            p_ (i + 1) ≤ ini.p →
                              p_ (i - 1) -
                                  k ^ (1 / 8 : ℝ) * αFunction k (height k ini.p (p_ (i - 1))) ≤
                                p_ (i + 1) := by
  filter_upwards [six_four_density μ₁ p₀ hμ₁ hp₀, six_five_red,
    top_adjuster (tendsto_natCast_atTop_atTop.eventually six_four_weak_aux)] with l hl hr hk k hlk
    μ hμl hμu n χ ini hini i hi hi'
  simp only [mem_union, or_assoc] at hi
  rcases hi with (hir | hib | his)
  rotate_left
  · exact six_four_blue (hμ₀.trans_le hμl) hib
  · refine' (hl k hlk μ hμu n χ ini hini i his).trans' _
    rw [sub_le_iff_le_add]
    have := densitySteps_sub_one_mem_degree his
    refine' (six_four_degree this.2).trans _
    rw [Nat.sub_add_cancel this.1, le_add_iff_nonneg_right]
    exact mul_nonneg (rpow_nonneg (Nat.cast_nonneg _) _) (α_nonneg _ _)
  refine' (six_four_red hir).trans' _
  have hirs := redSteps_sub_one_mem_degree hir
  have := six_four_degree hirs.2
  rw [Nat.sub_add_cancel hirs.1] at this
  refine' sub_le_sub this _
  have := hr k hlk μ n χ ini i hir
  rw [height_eq_one hi', tsub_le_iff_right] at this
  have :
    height k ini.p (algorithm μ k l ini i).p ≤
      height k ini.p (algorithm μ k l ini (i - 1)).p + 2 := by
    refine' this.trans _
    rw [add_le_add_iff_right]
    exact one_le_height
  refine' (α_increasing this).trans _
  rw [αFunction, αFunction, mul_div_assoc']
  refine' div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [mul_left_comm]
  refine' mul_le_mul_of_nonneg_left _ (rpow_nonneg (Nat.cast_nonneg _) _)
  exact hk _ hlk _ one_le_height

theorem six_two_part_one {f : ℕ → ℝ} {j j' : ℕ} (hj : Odd j) (hj' : Odd j') (hjj : j' ≤ j) :
    f (j' + 1) - f (j + 1) = ∑ i ∈ (Finset.Icc (j' + 2) j).filter Odd, (f (i - 1) - f (i + 1)) := by
  obtain ⟨j, rfl⟩ := hj.exists_bit1
  obtain ⟨j', rfl⟩ := hj'.exists_bit1
  replace hjj : j' ≤ j := by omega
  have hinj : Function.Injective fun n : ℕ => 2 * n + 1 := by
    intro i i' h
    dsimp at h
    omega
  have :
    (Icc (2 * j' + 1 + 2) (2 * j + 1)).filter Odd =
      (Icc (j' + 1) j).map ⟨fun n => 2 * n + 1, hinj⟩ := by
    ext i
    simp only [mem_filter, mem_Icc, Finset.mem_map, odd_iff_exists_bit1,
      Function.Embedding.coeFn_mk, and_assoc]
    constructor
    · rintro ⟨hi, hi', i, rfl⟩
      exact ⟨i, by omega, by omega, rfl⟩
    rintro ⟨i, hi, hi', rfl⟩
    exact ⟨by omega, by omega, i, rfl⟩
  rw [this, sum_map, ← Finset.Ico_succ_right_eq_Icc, sum_Ico_eq_sum_range,
    Order.succ_eq_add_one, Nat.add_sub_add_right]
  simp only [Function.Embedding.coeFn_mk]
  have :
    ∀ k : ℕ,
      f (2 * ((j' + 1) + k) + 1 - 1) - f (2 * ((j' + 1) + k) + 1 + 1) =
        f (2 * ((j' + 1) + k)) - f (2 * ((j' + 1) + (k + 1))) := by
    intro k
    rw [Nat.add_sub_cancel]
    simp only [mul_add, add_assoc, mul_one]
  simp only [this]
  rw [sum_range_sub']
  grind

theorem sum_le_of_nonneg {α : Type*} {f : α → ℝ} {s : Finset α} :
    ∑ x ∈ s, f x ≤ ∑ x ∈ (s.filter fun i => 0 < f i), f x := by
  rw [← sum_filter_add_sum_filter_not s fun i => 0 < f i, add_le_iff_nonpos_right]
  exact sum_nonpos (by simp (config := { contextual := true }))

theorem mem_union_of_odd {μ : ℝ} {i : ℕ} (hi : Odd i) (hi' : i < finalStep μ k l ini) :
    i ∈ redSteps μ k l ini ∪ ℬ ∪ 𝒮 := by
  rw [union_right_comm, redSteps_union_densitySteps, union_comm, bigBlueSteps,
    redOrDensitySteps, ← filter_or, mem_filter, mem_range, ← and_or_left, ← not_lt,
    and_iff_left (em' _), Nat.not_even_iff_odd, and_iff_left hi]
  exact hi'

theorem six_two_part_two {μ : ℝ} {k l : ℕ} {ini : BookConfig χ} {j j' : ℕ}
    (hjm : j < finalStep μ k l ini)
    (hij : ∀ i : ℕ, j' + 1 ≤ i → i ≤ j → Odd i → p_ (i - 1) ≤ ini.p) :
    ∑ i ∈ (Finset.Icc (j' + 2) j).filter Odd, (p_ (i - 1) - p_ (i + 1)) ≤
      ∑ i ∈ decreaseSteps μ k l ini, (p_ (i - 1) - p_ (i + 1)) := by
  have :
    ∑ i ∈ (Finset.Icc (j' + 2) j).filter Odd, (p_ (i - 1) - p_ (i + 1)) ≤
      ∑ i ∈ ((Finset.Icc (j' + 2) j).filter fun i => Odd i ∧ p_ (i + 1) < p_ (i - 1)),
        (p_ (i - 1) - p_ (i + 1)) := by
    rw [← filter_filter]
    refine' sum_le_of_nonneg.trans_eq _
    simp only [sub_pos]
  refine' this.trans _
  clear this
  refine' sum_le_sum_of_subset_of_nonneg _ _
  swap
  · simp only [mem_filter, mem_Icc, not_and, and_imp, sub_nonneg, decreaseSteps]
    intro i _ h _ _
    exact h.le
  intro i
  simp only [mem_filter, decreaseSteps, and_imp, mem_Icc]
  intro hi hi₁ hi₂ hi₃
  refine' ⟨_, hi₃, _⟩
  · exact mem_union_of_odd hi₂ (hi₁.trans_lt hjm)
  exact hij i (hi.trans' (Nat.le_succ _)) hi₁ hi₂

theorem six_two_part_three (μ₀ μ₁ p₀ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
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
                          ∀ j : ℕ,
                            j < finalStep μ k l ini →
                              Odd j →
                                (algorithm μ k l ini (j + 1)).p ≤ ini.p →
                                  ini.p ≤ (algorithm μ k l ini (j - 1)).p →
                                    ini.p - ε ≤ (algorithm μ k l ini (j + 1)).p := by
  filter_upwards [six_four_weak μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀, top_adjuster (eventually_ge_atTop 1)] with l
    hl hl₁ k hlk μ hμl hμu n χ hχ ini hini j hj hj₁ hj₂ hj₃
  have : j ∈ redSteps μ k l ini ∪ bigBlueSteps μ k l ini ∪ densitySteps μ k l ini :=
    mem_union_of_odd hj₁ hj
  refine' (hl k hlk μ hμl hμu n χ ini hini j this hj₂).trans' _
  have hj₄ : qFunction k ini.p 0 ≤ (algorithm μ k l ini (j - 1)).p := by
    rwa [qFunction_zero]
  rw [le_sub_comm]
  refine'
    (mul_le_mul_of_nonneg_left (five_seven_right hj₄)
          (rpow_nonneg (Nat.cast_nonneg _) _)).trans
      _
  rw [qFunction_zero, ← mul_assoc, ← sub_add, mul_add]
  refine' add_le_add _ _
  · refine' mul_le_of_le_one_left (sub_nonneg_of_le hj₃) _
    rw [← rpow_add' (Nat.cast_nonneg _)]
    refine' rpow_le_one_of_one_le_of_nonpos (Nat.one_le_cast.2 (hl₁ k hlk)) (by norm_num)
    norm_num1
  rw [mul_right_comm]
  refine' mul_le_of_le_one_left (rpow_nonneg (Nat.cast_nonneg _) _) _
  rw [mul_one_div, ← rpow_sub_one]
  · exact rpow_le_one_of_one_le_of_nonpos (Nat.one_le_cast.2 (hl₁ k hlk)) (by norm_num)
  rw [Nat.cast_ne_zero, ← pos_iff_ne_zero]
  exact hl₁ k hlk

theorem six_two_main (μ₀ μ₁ p₀ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
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
                          ∀ i : ℕ,
                            i < finalStep μ k l ini → i ∉ 𝒟 → ini.p - 3 * ε ≤ p_ (i + 1) := by
  filter_upwards [six_three μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀, six_two_part_three μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀] with l hl
    hl' k hlk μ hμl hμu n χ hχ ini hini j hj hj₁
  cases' le_or_gt ini.p (p_ (j + 1)) with h h
  · refine' h.trans' _
    rw [sub_le_self_iff]
    positivity
  have hj₂ : Odd j := by
    rw [degreeSteps, mem_filter, mem_range] at hj₁
    simpa only [hj, true_and, Nat.not_even_iff_odd] using hj₁
  let js := (range (j + 1)).filter fun j' => Odd j' ∧ ini.p ≤ p_ (j' - 1)
  have hjs : js.Nonempty := by
    rw [filter_nonempty_iff]
    refine' ⟨1, _, odd_one, _⟩
    · simp only [mem_range, lt_add_iff_pos_left]
      exact hj₂.pos
    dsimp
    rw [algorithm_zero]
  let j' : ℕ := js.max' hjs
  have hj' : j' ≤ j ∧ Odd j' ∧ ini.p ≤ p_ (j' - 1) := by
    simpa only [j', js, mem_filter, mem_range_succ_iff, and_imp] using
      Finset.max'_mem _ hjs
  have : ∀ i : ℕ, j' + 1 ≤ i → i ≤ j → Odd i → p_ (i - 1) ≤ ini.p := by
    intro i hi₁ hi₂ hi₃
    by_contra! hi₄
    have : i ∈ js := by
      rw [mem_filter, mem_range_succ_iff]
      exact ⟨hi₂, hi₃, hi₄.le⟩
    rw [Nat.succ_le_iff] at hi₁
    exact (Finset.le_max' _ _ this).not_gt hi₁
  have p_first : p_ (j' + 1) - 2 * ε ≤ p_ (j + 1) := by
    rw [sub_le_comm,
      six_two_part_one (f := fun i => (algorithm μ k l ini i).p) hj₂ hj'.2.1 hj'.1]
    refine' (six_two_part_two hj this).trans _
    exact hl k hlk μ hμl hμu n χ hχ ini hini
  refine' p_first.trans' _
  have : p_ (j' + 1) ≤ ini.p := by
    cases' eq_or_lt_of_le hj'.1 with hjj hjj
    · rw [hjj]
      exact h.le
    rw [← Nat.add_one_le_iff] at hjj
    refine' this (j' + 2) (Nat.le_succ _) _ (by simp [hj', parity_simps])
    cases' eq_or_lt_of_le hjj with hjj' hjj'
    · rw [← hjj'] at hj₂
      exfalso
      exact (Nat.odd_add_one.mp hj₂) hj'.2.1
    rw [Nat.add_one_le_iff]
    exact hjj'
  refine'
    (sub_le_sub_right
          (hl' k hlk μ hμl hμu n χ hχ ini hini j' (hj'.1.trans_lt hj) hj'.2.1 this hj'.2.2)
          _).trans'
      _
  rw [← two_add_one_eq_three, add_one_mul, sub_sub, add_comm]

theorem six_two (μ₀ μ₁ p₀ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
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
                        p₀ ≤ ini.p → ∀ i : ℕ, i ≤ finalStep μ k l ini → ini.p - 3 * ε ≤ p_ i := by
  filter_upwards [six_two_main μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀] with l hl k hlk μ hμl hμu n χ hχ ini hini i hi
  cases' i with i
  · rw [algorithm_zero, sub_le_self_iff]
    positivity
  rw [Nat.succ_le_iff] at hi
  by_cases h : i ∈ 𝒟
  · refine' (six_four_degree h).trans' _
    rw [degreeSteps, mem_filter, even_iff_exists_two_mul, mem_range] at h
    obtain ⟨rfl | i, rfl⟩ := h.2
    · dsimp
      rw [algorithm_zero, sub_le_self_iff]
      positivity
    have : 2 * i.succ = 2 * i + 1 + 1 := by rw [Nat.mul_succ, add_assoc]
    rw [this] at *
    refine' hl k hlk μ hμl hμu n χ hχ ini hini (2 * i + 1) _ _
    · exact hi.trans_le' (Nat.le_succ _)
    rw [degreeSteps, mem_filter]
    simp
  exact hl k hlk μ hμl hμu n χ hχ ini hini i hi h

theorem two_approx {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1 / 2) : 2 ^ (-2 * x) ≤ 1 - x := by
  have p : -2 * log 2 ≤ 0 := by simp [log_nonneg one_le_two]
  have hu₀ : x * (-2 * log 2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx p
  have hu₁ : -log 2 ≤ x * (-2 * log 2) := by nlinarith
  have := general_convex_thing' hu₀ hu₁ (neg_ne_zero.2 (log_pos one_lt_two).ne')
  rw [← mul_assoc, ← mul_assoc, div_neg, mul_div_cancel_right₀ _ (log_pos one_lt_two).ne', ←
    sub_eq_add_neg, mul_comm, ← rpow_def_of_pos zero_lt_two, mul_comm] at this
  refine' this.trans_eq _
  rw [Real.exp_neg, exp_log]
  · norm_num
    rw [mul_comm, mul_one_div, mul_div_cancel_left₀]
    norm_num1
  norm_num1

theorem six_one_ind (μ₀ μ₁ p₀ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
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
                          ∀ i,
                            i ≤ finalStep μ k l ini →
                              ((1 - (k : ℝ) ^ (-1 / 8 : ℝ)) * (ini.p - 3 * ε)) ^
                                    (redOrDensitySteps μ k l ini ∩ range i).card *
                                  ini.Y.card ≤
                                (algorithm μ k l ini i).Y.card := by
  have h₄ : (0 : ℝ) < 1 / 4 := by norm_num
  have t : Tendsto (Nat.cast : ℕ → ℝ) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [top_adjuster
      (((tendsto_rpow_neg_atTop h₄).comp t).eventually
        (eventually_le_nhds (by positivity : 0 < p₀ / 3))),
    top_adjuster (eventually_ge_atTop 1), top_adjuster (t.eventually_ge_atTop p₀⁻¹),
    six_two μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀] with l hl hl' hl₂ hl₃ k hlk μ hμl hμu n χ hχ ini hini i hi
  induction' i with i ih
  · rw [range_zero, inter_empty, card_empty, pow_zero, one_mul, algorithm_zero]
  rw [Nat.succ_le_iff] at hi
  have hi' := hi
  rw [← mem_range, ← union_partial_steps, mem_union, mem_union, or_assoc, or_rotate] at hi'
  rw [range_add_one]
  rcases hi' with (hib | hid | hirs)
  · have hi'' := Finset.disjoint_left.1 bigBlueSteps_disjoint_redOrDensitySteps hib
    rw [inter_insert_of_notMem hi'']
    refine' (ih hi.le).trans_eq _
    rw [big_blue_applied hib, BookConfig.bigBlueStep_Y]
  · have hi'' :=
      Finset.disjoint_left.1 degreeSteps_disjoint_bigBlueSteps_union_redOrDensitySteps hid
    rw [mem_union, not_or] at hi''
    rw [inter_insert_of_notMem hi''.2]
    refine' (ih hi.le).trans_eq _
    rw [degree_regularisation_applied hid, BookConfig.degreeRegularisationStep_Y]
  rw [inter_insert_of_mem hirs, card_insert_of_notMem, pow_succ', mul_assoc]
  swap
  · simp
  have hk₈ : (0 : ℝ) ≤ 1 - k ^ (-1 / 8 : ℝ) := by
    rw [sub_nonneg]
    refine' rpow_le_one_of_one_le_of_nonpos _ (by norm_num)
    rw [Nat.one_le_cast]
    exact hl' k hlk
  refine' (mul_le_mul_of_nonneg_left (ih hi.le) (mul_nonneg _ _)).trans _
  · exact hk₈
  · rw [sub_nonneg]
    refine' hini.trans' _
    rw [← le_div_iff₀', neg_div]
    · exact hl k hlk
    norm_num1
  have hd : 1 ≤ i ∧ i - 1 ∈ degreeSteps μ k l ini := redOrDensitySteps_sub_one_mem_degree hirs
  have :
    (algorithm μ k l ini i.succ).Y = red_neighbors χ (getX hirs) ∩ (algorithm μ k l ini i).Y := by
    rw [← redSteps_union_densitySteps, mem_union] at hirs
    cases' hirs with hir his
    · rw [red_applied hir, BookConfig.redStepBasic_Y]
    · rw [density_applied his, BookConfig.densityBoostStepBasic_Y]
  rw [this]
  have hp₀' : (1 : ℝ) / k ≤ ini.p := by
    refine' hini.trans' _
    rw [one_div]
    exact inv_le_of_inv_le₀ hp₀ (hl₂ k hlk)
  have := five_eight hp₀' hd.2 (getX hirs)
  rw [Nat.sub_add_cancel hd.1] at this
  refine' (this (BookConfig.getCentralVertex_mem_x _ _ _)).trans' _
  refine' mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  refine' mul_le_mul_of_nonneg_left _ hk₈
  exact hl₃ k hlk μ hμl hμu n χ hχ ini hini (i - 1) ((Nat.sub_le _ _).trans hi.le)

theorem six_one_ind_rearranged (μ₀ μ₁ p₀ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
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
                          ∀ i,
                            i ≤ finalStep μ k l ini →
                              ((1 - (k : ℝ) ^ (-1 / 8 : ℝ)) * (1 - 3 * ε / ini.p)) ^ (2 * k) *
                                    ini.p ^
                                      ((redSteps μ k l ini ∩ range i).card +
                                        (densitySteps μ k l ini ∩ range i).card) *
                                  ini.Y.card ≤
                                (algorithm μ k l ini i).Y.card := by
  have h₅ : (0 : ℝ) < 1 / 4 := by norm_num
  have h₆ :=
    ((tendsto_rpow_neg_atTop h₅).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_le_nhds (by positivity : 0 < p₀ / 3))
  filter_upwards [six_one_ind μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀, top_adjuster (eventually_gt_atTop 0),
    top_adjuster h₆] with l hl hl₀ hl' k hlk μ hμl hμu n χ hχ ini hini i hi
  specialize hl k hlk μ hμl hμu n χ hχ ini hini i hi
  refine' hl.trans' (mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _))
  have h₁ :
    (redSteps μ k l ini ∩ range i).card + (densitySteps μ k l ini ∩ range i).card ≤ 2 * k := by
    rw [two_mul]
    refine' add_le_add _ _
    · refine' (card_le_card inter_subset_left).trans _
      exact four_four_red μ hχ ini
    · refine' (card_le_card inter_subset_left).trans _
      have := four_four_blue_density μ (hl₀ _ hlk).ne' (hl₀ _ le_rfl).ne' hχ ini
      exact hlk.trans' (this.trans' le_add_self)
  have h₂ :
    (redSteps μ k l ini ∩ range i).card + (densitySteps μ k l ini ∩ range i).card =
      (redOrDensitySteps μ k l ini ∩ range i).card := by
    rw [← card_union_of_disjoint, ← redSteps_union_densitySteps, union_inter_distrib_right]
    exact redSteps_disjoint_densitySteps.mono inter_subset_left inter_subset_left
  have hp₀' : 0 < ini.p := hp₀.trans_le hini
  have h₃ : (0 : ℝ) ≤ 1 - k ^ (-1 / 8 : ℝ) := by
    refine' sub_nonneg_of_le (rpow_le_one_of_one_le_of_nonpos _ (by norm_num1))
    rw [Nat.one_le_cast]
    exact hl₀ k hlk
  have h₄ : (0 : ℝ) ≤ 1 - 3 * k ^ (-1 / 4 : ℝ) / ini.p := by
    rw [sub_nonneg]
    refine' div_le_one_of_le₀ (hini.trans' _) hp₀'.le
    rw [← le_div_iff₀', neg_div]
    · exact hl' k hlk
    norm_num1
  refine' (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one _ _ h₁) _).trans _
  · refine' mul_nonneg h₃ h₄
  · refine' mul_le_one₀ _ h₄ _
    · rw [sub_le_self_iff]
      positivity
    · rw [sub_le_self_iff]
      positivity
  · exact pow_nonneg hp₀'.le _
  rw [h₂, ← mul_pow, mul_assoc, one_sub_mul _ ini.p, div_mul_cancel₀ _ hp₀'.ne']

open Asymptotics

theorem six_one_error (p₀ : ℝ) (hp₀ : 0 < p₀) :
    ∃ f : ℕ → ℝ,
      (f =o[atTop] fun i => (i : ℝ)) ∧
        ∀ᶠ k : ℕ in atTop,
          ∀ p,
            p₀ ≤ p →
              (2 : ℝ) ^ f k ≤ ((1 - (k : ℝ) ^ (-1 / 8 : ℝ)) * (1 - 3 * ε / p)) ^ (2 * k) := by
  let g : ℝ → ℝ := fun k => -2 * k ^ (-1 / 8 : ℝ) - 2 * (3 * k ^ (-1 / 4 : ℝ) / p₀)
  refine' ⟨fun k : ℕ => g k * (2 * k), _, _⟩
  · suffices g =o[atTop] fun x => (1 : ℝ) by
      have := this.comp_tendsto tendsto_natCast_atTop_atTop
      refine' (this.mul_isBigO (isBigO_const_mul_self (2 : ℝ) _ atTop)).congr_right _
      simp only [Function.comp_apply, one_mul, implies_true]
    refine' IsLittleO.sub _ _
    · refine' IsLittleO.const_mul_left _ _
      simpa using isLittleO_rpow_rpow (by norm_num : -1 / 8 < (0 : ℝ))
    · simp_rw [div_eq_mul_one_div (_ * _), mul_comm _ (1 / p₀), ← mul_assoc]
      refine' IsLittleO.const_mul_left _ _
      simpa using isLittleO_rpow_rpow (by norm_num : -1 / 4 < (0 : ℝ))
  have t : Tendsto (Nat.cast : ℕ → ℝ) atTop atTop := tendsto_natCast_atTop_atTop
  have h₈ := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 8)
  have h₄ := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)
  filter_upwards [(h₄.comp t).eventually (eventually_le_nhds (by positivity : 0 < p₀ / (2 * 3))),
    (h₈.comp t).eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with k hk₄ hk₈ p
    hp
  rw [rpow_mul, ← Nat.cast_two, ← Nat.cast_mul, Nat.cast_two, rpow_natCast]
  swap
  · exact two_pos.le
  refine' pow_le_pow_left₀ (rpow_nonneg two_pos.le _) _ _
  have h₁ : (2 : ℝ) ^ (-2 * (k : ℝ) ^ (-1 / 8 : ℝ)) ≤ 1 - (k : ℝ) ^ (-1 / 8 : ℝ) := by
    refine' two_approx (rpow_nonneg (Nat.cast_nonneg _) _) _
    rwa [neg_div]
  have h₂ :
    (2 : ℝ) ^ (-2 * (3 * (k : ℝ) ^ (-1 / 4 : ℝ) / p₀)) ≤ 1 - 3 * (k : ℝ) ^ (-1 / 4 : ℝ) / p := by
    refine' (two_approx (by positivity) _).trans _
    · rw [div_le_iff₀' hp₀, mul_one_div, ← le_div_iff₀', div_div, neg_div]
      · exact hk₄
      · norm_num1
    rw [sub_le_sub_iff_left]
    exact div_le_div_of_nonneg_left (by positivity) hp₀ hp
  refine' (mul_le_mul h₁ h₂ (rpow_nonneg two_pos.le _) _).trans_eq' _
  · exact h₁.trans' (rpow_nonneg two_pos.le _)
  rw [← rpow_add two_pos, neg_mul _ (_ / _), ← sub_eq_add_neg]

theorem six_one_general (p₀ : ℝ) (hp₀ : 0 < p₀) :
    ∃ f : ℕ → ℝ,
      (f =o[atTop] fun i => (i : ℝ)) ∧
        ∀ μ₀ μ₁ : ℝ,
          0 < μ₀ →
            μ₁ < 1 →
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
                                    ∀ i,
                                      i ≤ finalStep μ k l ini →
                                        (2 : ℝ) ^ f k *
                                              ini.p ^
                                                ((redSteps μ k l ini ∩ range i).card +
                                                  (densitySteps μ k l ini ∩ range i).card) *
                                            ini.Y.card ≤
                                          (algorithm μ k l ini i).Y.card := by
  obtain ⟨f, hf, hf'⟩ := six_one_error p₀ hp₀
  refine' ⟨f, hf, _⟩
  intro μ₀ μ₁ hμ₀ hμ₁
  filter_upwards [top_adjuster hf', six_one_ind_rearranged μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀] with l hl hl' k hlk
    μ hμl hμu n χ hχ ini hini i hi
  specialize hl' k hlk μ hμl hμu n χ hχ ini hini i hi
  specialize hl k hlk ini.p hini
  refine' hl'.trans' _
  rw [mul_assoc, mul_assoc]
  refine' mul_le_mul_of_nonneg_right hl (mul_nonneg _ (Nat.cast_nonneg _))
  exact pow_nonneg colDensity_nonneg _

theorem six_one (p₀ : ℝ) (hp₀ : 0 < p₀) :
    ∃ f : ℕ → ℝ,
      (f =o[atTop] fun i => (i : ℝ)) ∧
        ∀ μ₀ μ₁ : ℝ,
          0 < μ₀ →
            μ₁ < 1 →
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
                                    (2 : ℝ) ^ f k *
                                          ini.p ^
                                            ((redSteps μ k l ini).card +
                                              (densitySteps μ k l ini).card) *
                                        ini.Y.card ≤
                                      (endState μ k l ini).Y.card := by
  obtain ⟨f, hf, hf'⟩ := six_one_general p₀ hp₀
  refine' ⟨f, hf, _⟩
  intro μ₀ μ₁ hμ₀ hμ₁
  filter_upwards [hf' μ₀ μ₁ hμ₀ hμ₁] with l hl k hlk μ hμl hμu n χ hχ ini hini
  have h₁ : redSteps μ k l ini ∩ range (finalStep μ k l ini) = redSteps μ k l ini := by
    rw [inter_eq_left]
    exact redSteps_subset_redOrDensitySteps.trans (filter_subset _ _)
  have h₂ : densitySteps μ k l ini ∩ range (finalStep μ k l ini) = densitySteps μ k l ini := by
    rw [inter_eq_left]
    exact densitySteps_subset_redOrDensitySteps.trans (filter_subset _ _)
  specialize hl k hlk μ hμl hμu n χ hχ ini hini _ le_rfl
  rwa [h₁, h₂] at hl

end SimpleGraph
