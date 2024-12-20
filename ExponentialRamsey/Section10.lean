/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Section9

/-!
# Section 10
-/


namespace SimpleGraph

open scoped BigOperators ExponentialRamsey Nat Real

open Filter Finset Nat Real Asymptotics

theorem large_gamma_part_one_aux {γ η : ℝ} (h : γ ≤ 1 / 5) (hη : η ≤ 1 / 800 * γ) :
    (3199 / 4000) ^ (5 / 4 : ℝ) ≤ (1 - γ - η) ^ (1 / (1 - γ)) :=
  by
  refine'
    (nine_two_monotone (1 / 5) (3199 / 4000) h _ (by norm_num1) (by norm_num1)
          (by norm_num1)).trans_eq'
      _
  · linarith only [h, hη]
  norm_num1
  rfl

theorem large_gamma_part_one {γ η : ℝ} (h : γ ≤ 1 / 5) (hη : η ≤ 1 / 800 * γ) :
    exp (-1 / 3 + 1 / 20 + 1 / 480) ≤ (1 - γ - η) ^ (1 / (1 - γ)) :=
  by
  refine' (large_gamma_part_one_aux h hη).trans' _
  have : (0 : ℝ) < 3199 / 4000 := by norm_num1
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

theorem large_gamma_part_two {k t : ℕ} {γ η : ℝ} (hγl : 0 ≤ γ) (hγu : γ ≤ 1 / 5)
    (hηγ : η ≤ 1 / 800 * γ) (ht : (2 / 3 : ℝ) * k ≤ t) (hk : 0 < k)
    (h : exp (-1 / 3 + 1 / 20 + 1 / 480) ≤ (1 - γ - η) ^ (1 / (1 - γ))) :
    exp (250 / 3200 * (γ * t ^ 2 / k)) ≤
      exp (γ * t ^ 2 / (2 * k)) * (1 - γ - η) ^ (γ * t / (1 - γ)) :=
  by
  have : 0 < 1 - γ - η := by linarith only [hγu, hηγ]
  rw [div_eq_mul_one_div _ (1 - γ), mul_comm _ (1 / (1 - γ)), rpow_mul this.le]
  refine'
    (mul_le_mul_of_nonneg_left (rpow_le_rpow (exp_pos _).le h (by positivity))
          (exp_pos _).le).trans'
      _
  rw [← exp_one_rpow (_ + _), ← rpow_mul (exp_pos _).le, exp_one_rpow, ← Real.exp_add, exp_le_exp,
    sq, ← mul_assoc, mul_div_assoc, mul_div_assoc, mul_left_comm, mul_comm _ (γ * t), ← mul_add,
    div_add', div_mul_div_comm]
  swap; · positivity
  refine' mul_le_mul_of_nonneg_left _ (by positivity)
  rw [div_le_iff, div_mul_comm, mul_div_mul_right]
  · linarith
  · positivity
  · positivity

theorem large_gamma_part_three {k t : ℕ} {γ : ℝ} (hγl : 3 / 20 < γ) (ht : (2 / 3 : ℝ) * k ≤ t)
    (hk : 0 < k) : exp (-240 / 3200 * (γ * t ^ 2 / k)) ≤ exp (-(1 / 200) * k) :=
  by
  rw [exp_le_exp, neg_mul, neg_div, neg_mul, neg_le_neg_iff, mul_div_assoc', le_div_iff, ←
    mul_assoc]
  refine' (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_left _ ht 2) _).trans' _
  · positivity
  · positivity
  rw [mul_pow, ← mul_assoc (_ * γ), mul_assoc, ← sq (k : ℝ)]
  · refine' mul_le_mul_of_nonneg_right _ (by positivity)
    norm_num1
    linarith only [hγl]
  · positivity

theorem small_gamma_part_one_aux {γ η : ℝ} (h : γ ≤ 3 / 20) (hη : η ≤ 1 / 800 * γ) :
    (13597 / 16000) ^ (20 / 17 : ℝ) ≤ (1 - γ - η) ^ (1 / (1 - γ)) :=
  by
  refine'
    (nine_two_monotone (3 / 20) (13597 / 16000) h _ (by norm_num1) (by norm_num1)
          (by norm_num1)).trans_eq'
      _
  · linarith only [h, hη]
  norm_num1
  rfl

theorem small_gamma_part_one {γ η : ℝ} (h : γ ≤ 3 / 20) (hη : η ≤ 1 / 800 * γ) :
    exp (-1 / 3 + 37 / 480) ≤ (1 - γ - η) ^ (1 / (1 - γ)) :=
  by
  have : exp (-1 / 3 + 37 / 480) ≤ exp (-7 / 34) :=
    by
    rw [exp_le_exp]
    norm_num
  refine' (small_gamma_part_one_aux h hη).trans' (this.trans _)
  have : (0 : ℝ) < 13597 / 16000 := by norm_num1
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

theorem small_gamma_part_two {k t : ℕ} {γ η : ℝ} (hγl : 0 ≤ γ) (hγu : γ ≤ 3 / 20)
    (hηγ : η ≤ 1 / 800 * γ) (ht : (2 / 3 : ℝ) * k ≤ t) (hk : 0 < k)
    (h : exp (-1 / 3 + 37 / 480) ≤ (1 - γ - η) ^ (1 / (1 - γ))) :
    exp (370 / 3200 * (γ * t ^ 2 / k)) ≤
      exp (γ * t ^ 2 / (2 * k)) * (1 - γ - η) ^ (γ * t / (1 - γ)) :=
  by
  have : 0 < 1 - γ - η := by linarith only [hγu, hηγ]
  rw [div_eq_mul_one_div _ (1 - γ), mul_comm _ (1 / (1 - γ)), rpow_mul this.le]
  refine'
    (mul_le_mul_of_nonneg_left (rpow_le_rpow (exp_pos _).le h (by positivity))
          (exp_pos _).le).trans'
      _
  rw [← exp_one_rpow (_ + _), ← rpow_mul (exp_pos _).le, exp_one_rpow, ← Real.exp_add, exp_le_exp,
    sq, ← mul_assoc, mul_div_assoc, mul_div_assoc, mul_left_comm, mul_comm _ (γ * t), ← mul_add,
    div_add', div_mul_div_comm]
  swap; · positivity
  refine' mul_le_mul_of_nonneg_left _ (by positivity)
  rw [div_le_iff, div_mul_comm, mul_div_mul_right]
  · linarith
  · positivity
  · positivity

theorem small_gamma_part_three {k t : ℕ} {γ : ℝ} (hγl : 1 / 10 ≤ γ) (ht : (2 / 3 : ℝ) * k ≤ t)
    (hk : 0 < k) : exp (-360 / 3200 * (γ * t ^ 2 / k)) ≤ exp (-(1 / 200) * k) :=
  by
  -- 9 / 80
  rw [exp_le_exp, neg_mul, neg_div, neg_mul, neg_le_neg_iff, mul_div_assoc', le_div_iff, ←
    mul_assoc]
  refine' (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_left _ ht 2) _).trans' _
  · positivity
  · positivity
  rw [mul_pow, ← mul_assoc (_ * γ), mul_assoc, ← sq (k : ℝ)]
  · refine' mul_le_mul_of_nonneg_right _ (by positivity)
    norm_num1
    linarith only [hγl]
  · positivity

theorem ten_two_exp_approx {η γ : ℝ} (hγu : γ ≤ 1 / 5) (hγl : 0 ≤ η) (hηγ : η ≤ 1 / 800 * γ) :
    exp (-3 * η / 2) ≤ (1 - γ - η) / (1 - γ) :=
  by
  rw [← one_sub_div, ← div_mul_eq_mul_div]
  swap; · linarith
  have h₂ : -1 / 5 ≤ -3 / 2 * η := by linarith
  refine' (general_convex_thing' (by linarith) h₂ (by norm_num)).trans _
  have : 1 + -5 / 4 * η ≤ 1 - η / (1 - γ) :=
    by
    rw [neg_div, neg_mul, ← sub_eq_add_neg, sub_le_sub_iff_left, div_eq_mul_one_div, mul_comm]
    refine' mul_le_mul_of_nonneg_right _ hγl
    rw [div_le_iff] <;> linarith
  refine' this.trans' _
  rw [← mul_assoc, ← div_mul_eq_mul_div, add_le_add_iff_left]
  refine' mul_le_mul_of_nonneg_right _ hγl
  suffices exp (-1 / 5) ≤ 5 / 6
    by
    rw [mul_div_assoc, ← le_div_iff, sub_le_iff_le_add]
    · exact this.trans_eq (by norm_num1)
    · norm_num1
  refine' le_of_pow_le_pow 5 (by norm_num1) (by norm_num1) _
  rw [← exp_nat_mul, Nat.cast_bit1, Nat.cast_two, mul_div_cancel', ← inv_div, inv_pow, Real.exp_neg]
  · refine' inv_le_inv_of_le (by norm_num1) (exp_one_gt_d9.le.trans' (by norm_num1))
  · norm_num1

theorem ten_two_exp_approx_more {k t : ℕ} {η γ : ℝ} (hγu : γ ≤ 1 / 5) (hγl : 0 ≤ η)
    (hηγ : η ≤ 1 / 800 * γ) (ht : (2 / 3 : ℝ) * k ≤ t) (hk : 0 < k) :
    exp (-9 / 3200 * (γ * t ^ 2 / k)) ≤ ((1 - γ - η) / (1 - γ)) ^ t :=
  by
  refine' (pow_le_pow_of_le_left (exp_pos _).le (ten_two_exp_approx hγu hγl hηγ) _).trans' _
  rw [← exp_nat_mul, exp_le_exp, neg_div, neg_mul, neg_mul, neg_div, mul_neg, neg_le_neg_iff, sq, ←
    div_mul_eq_mul_div, mul_div_assoc', le_div_iff, mul_comm _ η, mul_assoc, mul_assoc,
    mul_left_comm γ t, mul_left_comm (_ / _ : ℝ) t]
  swap; · positivity
  refine' mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  refine' (mul_le_mul_of_nonneg_right hηγ (by positivity)).trans _
  rw [mul_assoc, mul_left_comm, mul_left_comm _ γ]
  exact mul_le_mul_of_nonneg_left (by linarith only [ht]) (by linarith only [hγl, hηγ])

theorem ten_two_end {k t : ℕ} {γ η fk : ℝ} (hγ₀' : 0 < γ) (ht : (2 / 3 : ℝ) * k ≤ t) (hk : 0 < k)
    (hγl : 1 / 10 ≤ γ) (hγu : γ ≤ 1 / 5) (hη : 0 ≤ η) (hηγ : η ≤ 1 / 800 * γ)
    (hfk : -fk ≤ 1 / 72000 * k) :
    1 ≤
      Real.exp (-(1 / 200) * k + fk) * (1 - γ - η) ^ (γ * t / (1 - γ)) *
          ((1 - γ - η) / (1 - γ)) ^ t *
        exp (γ * t ^ 2 / (2 * k)) :=
  by
  rw [mul_right_comm]
  refine' (mul_le_mul_of_nonneg_left (ten_two_exp_approx_more hγu hη hηγ ht hk) _).trans' _
  · refine' mul_nonneg (mul_nonneg (exp_pos _).le _) (exp_pos _).le
    refine' rpow_nonneg_of_nonneg _ _
    linarith only [hηγ, hγu]
  rw [mul_right_comm (Real.exp _), mul_assoc (Real.exp _), mul_right_comm, add_comm, Real.exp_add,
    mul_right_comm (Real.exp _)]
  have : 0 ≤ fk + 1 / 3200 * (γ * t ^ 2 / k) :=
    by
    rw [← neg_le_iff_add_nonneg']
    refine' hfk.trans _
    rw [mul_div_assoc', le_div_iff, mul_assoc, ← sq]
    refine'
      (mul_le_mul_of_nonneg_left
            (mul_le_mul hγl (pow_le_pow_of_le_left (by positivity) ht _) (sq_nonneg _) hγ₀'.le)
            (by norm_num1)).trans_eq'
        _
    · rw [mul_pow, ← mul_assoc, ← mul_assoc]
      norm_num
    rwa [Nat.cast_pos]
  cases le_or_lt γ (3 / 20)
  · refine'
      (mul_le_mul_of_nonneg_left
            (small_gamma_part_two hγ₀'.le h hηγ ht hk (small_gamma_part_one h hηγ))
            (by positivity)).trans'
        _
    rw [mul_right_comm]
    refine' (mul_le_mul_of_nonneg_left (small_gamma_part_three hγl ht hk) (by positivity)).trans' _
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, one_le_exp_iff]
    linarith only [this]
  · refine'
      (mul_le_mul_of_nonneg_left
            (large_gamma_part_two hγ₀'.le hγu hηγ ht hk (large_gamma_part_one hγu hηγ))
            (by positivity)).trans'
        _
    rw [mul_right_comm]
    refine' (mul_le_mul_of_nonneg_left (large_gamma_part_three h ht hk) (by positivity)).trans' _
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, one_le_exp_iff]
    linarith only [this]

open Finset

theorem ten_two :
    ∀ᶠ l : ℕ in atTop,
      ∀ k : ℕ,
        ∀ γ η : ℝ,
          γ = l / (k + l) →
            1 / 10 ≤ γ →
              γ ≤ 1 / 5 →
                0 ≤ η →
                  η ≤ 1 / 800 * γ →
                    ∀ n : ℕ,
                      ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                        1 - γ - η ≤ χ.density 0 →
                          exp (-(1 / 200) * (k : ℝ)) * (k + l).choose l ≤ n →
                            ∃ (m : Finset (Fin n)) (c : Fin 2),
                              χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card :=
  by
  have hγ₀ : (0 : ℝ) < 1 / 10 := by norm_num1
  obtain ⟨f, hf, hf'⟩ := nine_five
  filter_upwards [nine_three_lower_n (1 / 10) hγ₀, nine_three _ hγ₀, hf' _ hγ₀,
    top_adjuster (eventually_gt_at_top 0),
    top_adjuster (hf.bound (by norm_num1 : (0 : ℝ) < 1 / 72000))] with l hn₂ h₉₃ h₉₅ hk₀ hfk k γ η
    hγ hγl hγu hη hηγ n χ hχd hn
  clear hf'
  have hγ₁ : γ < 1 := hγu.trans_lt (by norm_num1)
  have hl₀ : 0 < l := hk₀ l le_rfl
  have hlk := le_of_gamma_le_half hγ hl₀ (hγu.trans (by norm_num1))
  have hγ₀' : 0 < γ := hγ₀.trans_le hγl
  have hγ' : 1 / 200 ≤ γ / 20 := by linarith only [hγl]
  have hδ : 1 / 200 = min (1 / 200) (γ / 20) :=
    by
    rw [min_eq_left]
    exact hγ'
  by_contra hχ
  have hp₀ : 1 / 2 ≤ 1 - γ - η := by linarith only [hγu, hηγ]
  specialize hn₂ k γ hγ hγl hγ₁ hlk _ le_rfl n (hn.trans' _)
  · refine' mul_le_mul_of_nonneg_right (exp_le_exp.2 _) (Nat.cast_nonneg _)
    refine' mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    exact neg_le_neg hγ'
  obtain ⟨ini, hini, hXc, hYc⟩ := exists_equibipartition_col_density χ hn₂
  replace hini := hχd.trans hini
  have hini4 : 1 / 4 ≤ ini.p := hini.trans' (hp₀.trans' (by norm_num1))
  specialize h₉₃ k hlk γ hγ hγl (hγu.trans (by norm_num1)) _ hδ n χ hχ ini hini4 hXc hn
  specialize h₉₅ k hlk γ (1 / 200) η hγ hγl (by norm_num1) hγ' hη hp₀ n χ hχ ini hini hYc hn
  specialize hfk k hlk
  rw [norm_eq_abs, abs_le', norm_coe_nat] at hfk
  have := ten_two_end hγ₀' h₉₃ (hl₀.trans_le hlk) hγl hγu hη hηγ hfk.2
  replace h₉₅ := h₉₅.trans' (mul_le_mul_of_nonneg_right this (Nat.cast_nonneg _))
  rw [one_mul, Nat.cast_le, ← Nat.choose_symm_add] at h₉₅
  have := ramsey_number_le_finset (ramsey_number_le_choose'.trans h₉₅) χ
  simp only [Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, tsub_le_iff_left,
    Matrix.head_cons] at this hχ
  obtain ⟨m, ⟨hm₀, hm₁, hm₂⟩ | ⟨hm₀, hm₁, hm₂⟩⟩ := this
  swap
  · exact hχ ⟨m, Or.inr ⟨hm₁, hm₂⟩⟩
  refine' hχ ⟨(end_state γ k l ini).A ∪ m, Or.inl ⟨_, hm₂.trans _⟩⟩
  · rw [Finset.coe_union, TopEdgeLabelling.MonochromaticOf_union]
    refine' ⟨(end_state γ k l ini).red_a, hm₁, _⟩
    exact
      (end_state γ k l ini).red_XYA.symm.subset_right (hm₀.trans (Finset.subset_union_right _ _))
  rwa [Finset.card_union_eq, add_le_add_iff_right]
  · exact t_le_A_card γ k l ini
  exact (end_state γ k l ini).hYA.symm.mono_right hm₀

theorem ten_two_variant :
    ∀ᶠ l : ℕ in atTop,
      ∀ k : ℕ,
        ∀ γ η : ℝ,
          γ = l / (k + l) →
            1 / 10 ≤ γ →
              γ ≤ 1 / 5 →
                0 ≤ η →
                  η ≤ 1 / 800 * γ →
                    ∀ V : Type*,
                      DecidableEq V →
                        Fintype V →
                          ∀ χ : TopEdgeLabelling V (Fin 2),
                            1 - γ - η ≤ χ.density 0 →
                              exp (-(1 / 200 : ℝ) * k) * (k + l).choose l ≤ Fintype.card V →
                                ∃ (m : Finset V) (c : Fin 2),
                                  χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card :=
  by
  filter_upwards [ten_two] with l hl k γ η hγ hγl hγu hη hηγ V _ _ χ hχ hn
  skip
  obtain ⟨e⟩ := Fintype.truncEquivFin V
  let χ' : TopEdgeLabelling (Fin (Fintype.card V)) (Fin 2) := χ.pullback e.symm.to_embedding
  have : 1 - γ - η ≤ χ'.density 0 := by
    refine' hχ.trans_eq _
    rw [TopEdgeLabelling.density, TopEdgeLabelling.density, Rat.cast_inj]
    refine' density_graph_iso _
    exact (labelGraph_iso _ _).symm
  obtain ⟨m, c, hm, hmc⟩ := hl k γ η hγ hγl hγu hη hηγ (Fintype.card V) χ' this hn
  exact ⟨m.map e.symm.to_embedding, c, hm.map, hmc.trans_eq (Finset.card_map _).symm⟩

-- lemma nine_one_part_one {m : ℝ} (hm : 1 < m) :
--   (⌈(m / exp 1 : ℝ)⌉₊ : ℝ) < m :=
theorem gamma'_lt_one_tenth_iff {k l m : ℕ} (h : m ≤ l) (h' : 0 < k) :
    (l - m : ℝ) / (k + l - m) < 1 / 10 ↔ (l - k / 9 : ℝ) < m :=
  by
  rw [add_sub_assoc, div_lt_div_iff, one_mul, ← sub_lt_iff_lt_add, ← mul_sub_one, ← lt_div_iff,
    sub_lt_comm]
  · norm_num1; rfl
  · norm_num1
  · rw [← Nat.cast_sub h]
    positivity
  · norm_num1

theorem gamma'_lt_one_tenth_iff' {k l m : ℕ} (h : m ≤ l) (h' : 0 < k) (hkl : (k : ℝ) ≤ 9 * l) :
    (l - m : ℝ) / (k + l - m) < 1 / 10 ↔ ⌊(l - k / 9 : ℝ)⌋₊ < m :=
  by
  rw [gamma'_lt_one_tenth_iff h h', ← Nat.floor_lt]
  rw [sub_nonneg, div_le_iff']
  · exact hkl
  · positivity

theorem big_m_le_l {k l m : ℕ} (hm : m = ⌊(l - k / 9 : ℝ)⌋₊ + 1) (hkl : (k : ℝ) ≤ 9 * l)
    (hk : 0 < k) : m ≤ l :=
  by
  rw [hm, Nat.add_one_le_iff, Nat.floor_lt, sub_lt_self_iff]
  · positivity
  rw [sub_nonneg, div_le_iff']
  · exact hkl
  · positivity

theorem small_gap_for_next {k l m : ℕ} (hm : m = ⌊(l - k / 9 : ℝ)⌋₊ + 1) (hkl : (k : ℝ) ≤ 9 * l)
    (hk : 0 < k) : (1 / 10 : ℝ) - 1 / k ≤ (l - m : ℝ) / (k + l - m) :=
  by
  have hml : m ≤ l := big_m_le_l hm hkl hk
  have h₃ : (l - m : ℝ) / (k + l - m) < 1 / 10 :=
    by
    rw [gamma'_lt_one_tenth_iff' hml hk hkl, hm]
    simp
  have hm1 : 1 ≤ m := by
    rw [hm]
    simp
  have habove : 1 / 10 ≤ (l - (m - 1) : ℝ) / (k + l - (m - 1)) := by
    rw [← Nat.cast_one, ← Nat.cast_sub hm1, Nat.cast_one, ← not_lt,
      gamma'_lt_one_tenth_iff' (hml.trans' (Nat.sub_le _ _)) hk hkl, hm, Nat.add_sub_cancel, not_lt]
  rw [add_sub_assoc, ← Nat.cast_sub hml] at h₃ ⊢
  rw [add_sub_assoc, ← sub_add, ← Nat.cast_sub hml] at habove
  set b := l - m with hb
  clear_value b
  have h₁ : (0 : ℝ) < k + b := by positivity
  have h₂ : (0 : ℝ) < k + b + 1 := add_pos h₁ zero_lt_one
  have : (b + 1 : ℝ) / (k + b + 1) - b / (k + b) ≤ 1 / k :=
    by
    rw [div_sub_div _ _ h₂.ne' h₁.ne', div_le_div_iff (mul_pos h₂ h₁), ← sub_nonneg]
    · ring_nf
      positivity
    positivity
  rw [← add_assoc] at habove
  linarith only [habove, this]

-- lemma gamma_mul_k_le_m_of {k l m : ℕ} (h : m ≤ l) (h' : 0 < k)
--   (hg : (l - m : ℝ) / (k + l - m) < (l / (k + l)) ^ 2) :
--   (l / (k + l) : ℝ) * k ≤ m :=
-- begin
--   rw [gamma'_le_gamma_iff h h'] at hg,
--   refine hg.le.trans' _,
--   rw [div_mul_eq_mul_div, div_le_div_iff, ←sub_nonneg],
--   { ring_nf,
--     positivity },
--   { positivity },
--   { positivity },
-- end
theorem uLowerBoundRatio_lower_bound_ten {k l m n : ℕ} {δ : ℝ} (hml : m ≤ l)
    (hn : exp δ * (k + l).choose l ≤ n) :
    exp δ * ((k + l - m).choose k : ℝ) ≤ n * uLowerBoundRatio 0 k l m :=
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
  rw [add_zero, one_pow, mul_one]

theorem big_U' {U : ℕ} (hU : (801 : ℝ) ≤ U) : (U : ℝ) / (U - 1) * (1 + 0) ≤ 1 + 1 / 800 :=
  by-- have : (801 : ℝ) ≤ U, { exact (nat.cast_le.2 hU).trans_eq' (by norm_num1) },
    rw [div_mul_eq_mul_div, div_le_iff] <;>
    linarith

/- ./././Mathport/Syntax/Translate/Basic.lean:641:2: warning: expanding binder collection (i «expr ∉ » x) -/
theorem exists_good_clique (n k l : ℕ) (χ : TopEdgeLabelling (Fin n) (Fin 2)) :
    ∃ x : Finset (Fin n),
      IsGoodClique 0 k l χ x ∧
        ((x.card ≤ ⌊(l - k / 9 : ℝ)⌋₊ ∧
            ∀ (i) (_ : i ∉ x), IsGoodClique 0 k l χ (insert i x) → False) ∨
          x.card = ⌊(l - k / 9 : ℝ)⌋₊ + 1) :=
  by
  classical
  let s := finset.univ.filter fun x => is_good_clique 0 k l χ x ∧ x.card ≤ ⌊(l - k / 9 : ℝ)⌋₊ + 1
  have : s.nonempty := by
    refine' ⟨∅, _⟩
    simp [empty_is_good]
  obtain h := Finset.exists_maximal s this
  simp only [Finset.mem_filter, Finset.mem_univ, true_and_iff, Finset.lt_eq_subset, and_imp,
    exists_prop] at h
  obtain ⟨x, ⟨hx, hx₁⟩, hx₂⟩ := h
  rw [le_iff_eq_or_lt, Nat.lt_add_one_iff] at hx₁
  refine' ⟨x, hx, _⟩
  cases hx₁
  · exact Or.inr hx₁
  refine' Or.inl ⟨hx₁, _⟩
  intro i hi hi'
  refine' hx₂ _ hi' _ (Finset.ssubset_insert hi)
  rwa [Finset.card_insert_of_not_mem hi, add_le_add_iff_right]

-- lemma maximally_good_clique {n k l : ℕ} {ξ ξ' : ℝ} {χ : TopEdgeLabelling (fin n) (fin 2)}
--   (hξ : 0 ≤ ξ)
--   (hχ : ¬∃ (m : finset (fin n)) (c : fin 2), χ.MonochromaticOf ↑m c ∧ ![k, l] c ≤ m.card)
--   {x : finset (fin n)}
--   (hU : ((common_blues χ x).card : ℝ) / ((common_blues χ x).card - 1) * (1 + ξ) ≤ 1 + ξ')
--   (hU' : 2 ≤ (common_blues χ x).card)
--   (hx : is_good_clique ξ k l χ x)
--   (h : ∀ y : finset (fin n), is_good_clique ξ k l χ y → ¬ x ⊂ y) :
--   1 - (1 + ξ') * ((l - x.card : ℝ) / (k + l - x.card)) ≤
--     (χ.pullback (function.embedding.subType* : common_blues χ x ↪ fin n)).density 0 :=
-- lemma nine_one_end {k l n : ℕ} {χ : TopEdgeLabelling (fin n) (fin 2)} {x : finset (fin n)}
--   (hχ : ¬∃ (m : finset (fin n)) (c : fin 2), χ.MonochromaticOf ↑m c ∧ ![k, l] c ≤ m.card)
--   (hx : is_good_clique (1 / 16) k l χ x)
--   (h : ∃ (m : finset (fin n)) (c : fin 2), m ⊆ common_blues χ x ∧ χ.MonochromaticOf ↑m c ∧
--     ![k, l - x.card] c ≤ m.card) :
--   false :=
-- lemma nine_one_part_three {k l m n : ℕ} {γ γ' δ : ℝ} {χ : TopEdgeLabelling (fin n) (fin 2)}
--   (hχ : ¬∃ (m : finset (fin n)) (c : fin 2), χ.MonochromaticOf ↑m c ∧ ![k, l] c ≤ m.card)
--   (hml : m < l) (hk₀ : 0 < k)
--   (hγ : γ = l / (k + l)) (hδ : δ = γ / 20) (hγ' : γ' = (l - m) / (k + l - m))
--   (h : exp (-δ * k) * ((k + l).choose l) * U_lower_bound_ratio (1 / 16) k l m <
--     exp (-(γ' / 20) * k) * ↑((k + (l - m)).choose (l - m))) :
--   false :=
-- begin
--   have : ((l + k - m).choose _ : ℝ) / _ = _ := choose_ratio hml.le,
--   rw [←nat.cast_add, add_comm l, add_tsub_assoc_of_le hml.le, nat.choose_symm_add] at this,
--   rw [←not_le] at h,
--   refine h _,
--   rw [U_lower_bound_ratio, ←nat.cast_add, ←this, nat.choose_symm_add, mul_assoc, mul_div_assoc',
--     mul_div_cancel', ←mul_assoc],
--   swap,
--   { rw [nat.cast_ne_zero, ←pos_iff_ne_zero],
--     exact nat.choose_pos (by simp) },
--   refine mul_le_mul_of_nonneg_right _ (nat.cast_nonneg _),
--   refine (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_left (exp_pos _).le xi_numeric.le _)
--     (exp_pos _).le).trans' _,
--   rw [←exp_nat_mul, ←real.exp_add, exp_le_exp, hδ, neg_mul, neg_mul, neg_add_eq_sub,
--     le_sub_iff_add_le, neg_add_eq_sub, mul_one_div, div_mul_eq_mul_div, div_mul_eq_mul_div,
--     ←sub_div, hγ, hγ', ←sub_mul],
--   refine div_le_div_of_le (by norm_num1) _,
--   rw [←le_div_iff],
--   swap,
--   { rw [nat.cast_pos], exact hk₀ },
--   refine (sub_le_sub_left (div_le_div_of_le_left _ _ (sub_le_self _ _)) _).trans _,
--   { rw [sub_nonneg, nat.cast_le], exact hml.le },
--   { rw [add_sub_assoc, ←nat.cast_sub hml.le], positivity },
--   { exact nat.cast_nonneg _ },
--   rw [←sub_div, sub_sub_self],
--   exact div_le_div_of_le_left (nat.cast_nonneg _) (by positivity) (by simp),
-- end
-- lemma gamma'_le_gamma {k l m : ℕ} (hk : 0 < k) (h : m ≤ l) :
--   (l - m : ℝ) / (k + l - m) ≤ l / (k + l) :=
theorem nine_bound {k l : ℕ} {γ : ℝ} (hk : 0 < k) (hγ : γ = l / (k + l)) (hγl : 1 / 10 ≤ γ) :
    (k : ℝ) ≤ 9 * l := by
  have := small_k (by norm_num1) hγl hγ hk
  norm_num1 at this
  rwa [mul_comm] at this

-- 104 king george road, ware
theorem four_bound {k l : ℕ} {γ : ℝ} (hk : 0 < k) (hγ : γ = l / (k + l)) (hγu : γ ≤ 1 / 5) :
    (4 : ℝ) * l ≤ k :=
  by
  rw [hγ, div_le_div_iff, one_mul, ← sub_le_iff_le_add, ← mul_sub_one, mul_comm] at hγu
  · norm_num1 at hγu
    exact hγu
  · positivity
  · norm_num1

theorem big_l {k l m : ℕ} (hk9l : (k : ℝ) ≤ 9 * l) (h5lk : (4 : ℝ) * l ≤ k)
    (hm : m ≤ ⌊(l - k / 9 : ℝ)⌋₊) : (4 / 9 : ℝ) * l ≤ (l - m : ℝ) :=
  by
  have : (m : ℝ) ≤ l - k / 9 := by
    rw [← @Nat.cast_le ℝ] at hm
    exact hm.trans (Nat.floor_le (by linarith only [hk9l]))
  · linarith only [this, h5lk]
  norm_num1

theorem big_l' {k l m : ℕ} (hk9l : (k : ℝ) ≤ 9 * l) (h5lk : (4 : ℝ) * l ≤ k)
    (hm : m ≤ ⌊(l - k / 9 : ℝ)⌋₊) (hml : m ≤ l) : 4 * l / 9 ≤ l - m :=
  by
  rw [← @Nat.floor_div_eq_div ℝ, Nat.cast_mul, ← div_mul_eq_mul_div, ← @Nat.cast_le ℝ]
  refine' (Nat.floor_le (by positivity)).trans _
  rw [Nat.cast_sub hml]
  norm_num1
  exact big_l hk9l h5lk hm

theorem big_l'' {k l m : ℕ} (hk9l : (k : ℝ) ≤ 9 * l) (h5lk : (4 : ℝ) * l ≤ k)
    (hm : m = ⌊(l - k / 9 : ℝ)⌋₊) (hk : 0 < k) (hl : 9 ≤ l) : l / 3 ≤ l - (m + 1) :=
  by
  have : (m : ℝ) ≤ l - k / 9 := by rw [hm]; exact Nat.floor_le (by linarith only [hk9l])
  have hml : m < l := by
    rw [hm, ← @Nat.cast_lt ℝ]
    refine' (Nat.floor_le (by linarith only [hk9l])).trans_lt _
    rw [sub_lt_self_iff]
    positivity
  rw [← @Nat.floor_div_eq_div ℝ, Nat.cast_bit1, Nat.cast_one, ← @Nat.cast_le ℝ]
  refine' (Nat.floor_le (by positivity)).trans _
  rw [Nat.cast_sub hml, Nat.cast_add_one, ← sub_sub, le_sub_iff_add_le]
  refine' (big_l hk9l h5lk hm.le).trans' _
  have : (9 : ℝ) ≤ l := by exact_mod_cast hl
  linarith only [this]

theorem k_ratio {k l m : ℕ} (hk9l : (k : ℝ) ≤ 9 * l) (h5lk : (4 : ℝ) * l ≤ k)
    (hm : m ≤ ⌊(l - k / 9 : ℝ)⌋₊) : (1 + 4 / 81 : ℝ) * k ≤ (k + l - m : ℝ) := by
  linarith only [big_l hk9l h5lk hm, hk9l]

theorem silly_numeric : 801 * exp 1 ≤ (1 + 4 / 81) ^ 200 :=
  by
  have : 801 * exp 1 ≤ (1 + 4 / 84) ^ 170 :=
    by
    rw [← le_div_iff']
    refine' exp_one_lt_d9.le.trans (by norm_num1)
    norm_num1
  refine' this.trans _
  refine' (pow_le_pow_of_le_left _ _ _).trans (pow_le_pow _ _)
  all_goals norm_num1

theorem other_silly_numeric : 1 ≤ exp (-(1 / 200)) * (1 + 4 / 81) :=
  by
  refine' le_of_pow_le_pow 200 (by positivity) (by positivity) _
  rw [one_pow, mul_pow, ← exp_nat_mul, mul_neg, ← div_le_iff' (exp_pos _), one_div, Real.exp_neg,
    inv_inv]
  refine' silly_numeric.trans' _
  norm_num1
  exact le_mul_of_one_le_left (exp_pos _).le (by norm_num1)

theorem large_number {k l m : ℕ} {γ δ : ℝ} (hγu : γ ≤ 1 / 5) (hδ : δ = γ / 40) (hlm : m ≤ l)
    (h : (1 + 4 / 81 : ℝ) * k ≤ (k + l - m : ℝ)) (hk : 0 < k) (hk' : 200 ≤ k) :
    801 ≤ exp (-δ * k) * ((k + l - m).choose k : ℝ) :=
  by
  have h₁ : k ≤ k + l - m := by
    rw [add_tsub_assoc_of_le hlm]
    simp only [le_add_iff_nonneg_right, zero_le']
  have h₂ : exp (-(1 / 200)) ^ k ≤ exp (-δ * k) :=
    by
    rw [← exp_nat_mul, mul_comm, exp_le_exp, hδ]
    refine' mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    linarith only [hγu]
  have : (1 + 4 / 81 : ℝ) ^ k ≤ (k + l - m).choose k :=
    by
    refine' (pow_div_le_choose h₁).trans' _
    refine' pow_le_pow_of_le_left (by norm_num1) _ _
    rwa [le_div_iff, add_tsub_assoc_of_le hlm, Nat.cast_add, Nat.cast_sub hlm, add_sub_assoc']
    positivity
  refine' (mul_le_mul_of_le_of_le h₂ this (by positivity) (Nat.cast_nonneg _)).trans' _
  rw [← mul_pow]
  refine' (pow_le_pow other_silly_numeric hk').trans' _
  rw [mul_pow, ← exp_nat_mul, mul_neg, ← div_le_iff' (exp_pos _), Real.exp_neg, div_eq_mul_inv,
    inv_inv]
  refine' silly_numeric.trans' _
  norm_num1
  rfl

theorem Nat.tendsto_div_const_atTop {a : ℕ} (ha : a ≠ 0) : Tendsto (fun x => x / a) atTop atTop :=
  Monotone.tendsto_atTop_atTop (fun _ _ h => Nat.div_le_div_right h) fun _ =>
    ⟨_, (Nat.mul_div_left _ ha.bot_lt).ge⟩

theorem large_l : Tendsto (fun l : ℕ => 4 * l / 9) atTop atTop :=
  by
  refine' Monotone.tendsto_atTop_atTop _ _
  · intro i j h
    exact Nat.div_le_div_right (Nat.mul_le_mul_left _ h)
  intro b
  refine' ⟨b * 9, _⟩
  rw [← mul_assoc, Nat.mul_div_cancel]
  · exact Nat.le_mul_of_pos_left (by norm_num1)
  · norm_num1

theorem ten_one_a_end {k l m n : ℕ} {γ δ : ℝ} (hγ : γ ≤ 1 / 5) (hδ : δ = γ / 40) (hml : m < l)
    (hm : exp (-δ * k) * (k + l).choose l < n)
    (h₁₀₂ :
      (n : ℝ) * uLowerBoundRatio 0 k l m ≤ exp (-(1 / 200) * k) * (k + (l - m)).choose (l - m)) :
    False := by
  have : ((l + k - m).choose _ : ℝ) / _ = _ := choose_ratio hml.le
  rw [← Nat.cast_add, add_comm l, add_tsub_assoc_of_le hml.le, Nat.choose_symm_add] at this
  replace h₁₀₂ :=
    (mul_lt_mul_of_pos_right hm (U_lower_bound_ratio_pos (by norm_num1) hml.le)).trans_le h₁₀₂
  refine' h₁₀₂.not_le _
  rw [U_lower_bound_ratio, add_zero, one_pow, one_mul, ← Nat.cast_add, ← this, Nat.choose_symm_add,
    mul_assoc, mul_div_cancel']
  swap
  · rw [Nat.cast_ne_zero, ← pos_iff_ne_zero]
    exact Nat.choose_pos (by simp)
  refine' mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [exp_le_exp]
  refine' mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  linarith only [hγ, hδ]

/- ./././Mathport/Syntax/Translate/Basic.lean:641:2: warning: expanding binder collection (i «expr ∉ » x) -/
theorem ten_one_a (n k l : ℕ) (γ δ : ℝ) (hl₀ : 0 < l) (hk₈ : 200 ≤ l)
    (h₁₀₂ :
      ∀ l' : ℕ,
        4 * l / 9 ≤ l' →
          ∀ (k : ℕ) (γ η : ℝ),
            γ = l' / (k + l') →
              1 / 10 ≤ γ →
                γ ≤ 1 / 5 →
                  0 ≤ η →
                    η ≤ 1 / 800 * γ →
                      ∀ (V : Type) [DecidableEq V] [Fintype V] (χ : TopEdgeLabelling V (Fin 2)),
                        1 - γ - η ≤ χ.density 0 →
                          Real.exp (-(1 / 200) * k) * (k + l').choose l' ≤ Fintype.card V →
                            ∃ (m : Finset V) (c : Fin 2),
                              χ.MonochromaticOf m c ∧ ![k, l'] c ≤ m.card)
    (hγ : γ = l / (k + l)) (hγu : γ ≤ 1 / 5) (hδ : δ = γ / 40) (hlk : l ≤ k)
    (hk9l : (k : ℝ) ≤ 9 * l) (h5lk : (4 : ℝ) * l ≤ k) (χ : TopEdgeLabelling (Fin n) (Fin 2))
    (hχ : ¬∃ (m : Finset (Fin n)) (c : Fin 2), χ.MonochromaticOf (↑m) c ∧ ![k, l] c ≤ m.card)
    (hm : exp (-δ * k) * (k + l).choose l < n) (x : Finset (Fin n)) (hx : IsGoodClique 0 k l χ x)
    (hml : x.card < l) (hγ'_le_γ : (l - x.card : ℝ) / (k + l - x.card) ≤ l / (k + l))
    (hγ' : (l - x.card : ℝ) / (k + l - x.card) = ↑(l - x.card) / (↑k + ↑(l - x.card)))
    (hxy :
      x.card ≤ ⌊(l : ℝ) - k / 9⌋₊ ∧ ∀ (i) (_ : i ∉ x), IsGoodClique 0 k l χ (insert i x) → False) :
    False := by
  have h₁ := k_ratio hk9l h5lk hxy.1
  have h₂ := U_lower_bound_ratio_lower_bound_ten hml.le hm.le
  replace h₂ := (large_number hγu hδ hml.le h₁ (hl₀.trans_le hlk) (hk₈.trans hlk)).trans h₂
  replace h₂ := h₂.trans hx.2
  have h₃ : 2 ≤ (common_blues χ x).card :=
    by
    rw [← @Nat.cast_le ℝ, Nat.cast_two]
    exact h₂.trans' (by norm_num1)
  have := maximally_good_clique le_rfl hχ (big_U' h₂) h₃ hx hxy.2
  rw [one_add_mul, ← sub_sub] at this
  have h' := big_l' hk9l h5lk hxy.1 hml.le
  rw [← not_lt, ← gamma'_lt_one_tenth_iff' hml.le (hl₀.trans_le hlk) hk9l, not_lt] at hxy
  specialize
    h₁₀₂ (l - x.card) h' k ((l - x.card) / (k + l - x.card)) _ hγ' hxy.1
      (hγ'_le_γ.trans (hγu.trans_eq' hγ.symm)) (by linarith only [hxy.1]) le_rfl _ _ this
  replace h₁₀₂ := fun z => nine_one_end hχ hx (ramsey_number_le_finset_aux _ (h₁₀₂ z))
  rw [imp_false, not_le, Fintype.subtype_card, Finset.filter_mem_eq_inter, Finset.univ_inter] at
    h₁₀₂
  exact ten_one_a_end hγu hδ hml hm (hx.2.trans h₁₀₂.le)

theorem ten_one_b (n k l : ℕ) (γ δ : ℝ) (hl₀ : 0 < l) (hk₈ : 200 ≤ l)
    (h₉₁ :
      ∀ l' : ℕ,
        l / 3 ≤ l' →
          ∀ (k : ℕ) (γ δ : ℝ),
            γ = ↑l' / (↑k + ↑l') →
              1 / 20 ≤ γ →
                γ ≤ 1 / 10 →
                  δ = γ / 20 → (ramseyNumber ![k, l'] : ℝ) ≤ exp (-δ * k + 1) * (k + l').choose l')
    (hγu : γ ≤ 1 / 5) (hδ : δ = γ / 40) (hlk : l ≤ k) (hk9l : (k : ℝ) ≤ 9 * l)
    (h5lk : (4 : ℝ) * l ≤ k) (χ : TopEdgeLabelling (Fin n) (Fin 2))
    (hχ : ¬∃ (m : Finset (Fin n)) (c : Fin 2), χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card)
    (hm : exp (-δ * k + 21 / 20) * (k + l).choose l < n) (x : Finset (Fin n))
    (hx : IsGoodClique 0 k l χ x) (hml : x.card < l)
    (hγ' : (l - x.card : ℝ) / (k + l - x.card) = ↑(l - x.card) / (↑k + ↑(l - x.card)))
    (hxy : x.card = ⌊(l - k / 9 : ℝ)⌋₊ + 1) : False :=
  by
  have h₁ := small_gap_for_next hxy hk9l (hl₀.trans_le hlk)
  have h₂ : (l - x.card : ℝ) / (k + l - x.card) < 1 / 10 :=
    by
    rw [gamma'_lt_one_tenth_iff' hml.le (hl₀.trans_le hlk) hk9l, hxy]
    exact Nat.lt_succ_self _
  have h₃ : l / 3 ≤ l - x.card := by
    rw [hxy]
    exact big_l'' hk9l h5lk rfl (hl₀.trans_le hlk) (hk₈.trans' (by norm_num1))
  have h₄ : (1 / 20 : ℝ) ≤ (l - x.card) / (k + l - x.card) :=
    by
    refine' h₁.trans' _
    rw [le_sub_comm, one_div_le]
    · refine' (Nat.cast_le.2 (hk₈.trans hlk)).trans' _
      norm_num1
    · rw [Nat.cast_pos]; exact hl₀.trans_le hlk
    norm_num1
  specialize h₉₁ (l - x.card) h₃ k _ _ hγ' h₄ h₂.le rfl
  suffices (ramsey_number ![k, l - x.card] : ℝ) ≤ (common_blues χ x).card
    by
    rw [Nat.cast_le] at this
    exact nine_one_end hχ hx (ramsey_number_le_finset this χ)
  have := (U_lower_bound_ratio_lower_bound_ten hml.le hm.le).trans hx.2
  refine' this.trans' _
  refine' h₉₁.trans _
  rw [← Nat.choose_symm_add, Nat.add_sub_assoc hml.le]
  refine' mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [exp_le_exp, hδ, neg_mul, neg_mul, neg_add_eq_sub, neg_add_eq_sub, sub_le_sub_iff]
  have : 1 + γ / 40 * k ≤ 1 + 1 / (10 * 20) * k :=
    by
    rw [add_le_add_iff_left]
    refine' mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    norm_num1
    linarith only [hγu]
  refine' this.trans _
  have :
    (21 / 20 : ℝ) + (1 / 10 - 1 / k) / 20 * k ≤
      21 / 20 + (l - x.card) / (k + l - x.card) / 20 * k :=
    by
    rw [add_le_add_iff_left]
    refine' mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    exact div_le_div_of_le (by norm_num1) h₁
  refine' this.trans' _
  rw [sub_div, div_div, div_div, ← mul_comm (k : ℝ), ← mul_comm (k : ℝ), mul_sub, add_sub_assoc', ←
    sub_add_eq_add_sub, add_le_add_iff_right, mul_div_assoc', mul_div_mul_left]
  · norm_num1
  rw [Nat.cast_ne_zero, ← pos_iff_ne_zero]
  exact hl₀.trans_le hlk

theorem ten_one_precise (γ₀ : ℝ) (hγ₀ : 0 < γ₀) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k : ℕ,
        ∀ γ δ : ℝ,
          γ = l / (k + l) →
            γ₀ ≤ γ →
              γ ≤ 1 / 5 →
                δ = γ / 40 → (ramseyNumber ![k, l] : ℝ) ≤ exp (-δ * k + 2.05) * (k + l).choose l :=
  by
  filter_upwards [top_adjuster (eventually_ge_at_top 2), eventually_gt_at_top 0,
    eventually_ge_at_top 200, nine_one_precise γ₀ hγ₀,
    large_l.eventually (top_adjuster ten_two_variant),
    (nat.tendsto_div_const_at_top (show 3 ≠ 0 by norm_num1)).Eventually
      (top_adjuster (nine_one_precise (1 / 20) (by positivity)))] with
    l hk₂ hl₀ hk₈ hk₉₁ h₁₀₂ h₉₁ k γ δ hγ hγl hγu hδ
  cases' le_or_lt γ (1 / 10) with hγ₁₀ hγ₁₀
  · refine' (hk₉₁ k γ (2 * δ) hγ hγl hγ₁₀ (by linarith only [hδ])).trans _
    refine' mul_le_mul_of_nonneg_right (exp_le_exp.2 _) (Nat.cast_nonneg _)
    refine'
      add_le_add (mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _))
        (show (1 : ℝ) ≤ 2.05 by norm_num1)
    linarith only [hδ, hγl, hγ₀]
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
  suffices (n : ℝ) ≤ exp (-δ * k + 21 / 20) * (k + l).choose l
    by
    have h : (41 / 20 : ℝ) = 21 / 20 + 1 := by norm_num1
    rw [h, ← add_assoc, add_comm, Real.exp_add, mul_assoc, ← div_le_iff' (exp_pos _)]
    exact this.trans' (Nat.le_ceil _)
  by_contra' hm
  classical
  have := exists_good_clique n k l χ
  obtain ⟨x, hx, hxy⟩ := this
  have hml := good_clique_bound hχ hx
  let m := x.card
  have hk9l : (k : ℝ) ≤ 9 * l := nine_bound (hl₀.trans_le hlk) hγ hγ₁₀.le
  have h5lk : (4 : ℝ) * l ≤ k := four_bound (hl₀.trans_le hlk) hγ hγu
  have hγ'_le_γ : _ ≤ _ := gamma'_le_gamma (hl₀.trans_le hlk) hml.le
  have hγ' : (l - m : ℝ) / (k + l - m) = ↑(l - x.card) / (↑k + ↑(l - x.card)) := by
    rw [Nat.cast_sub hml.le, add_sub_assoc]
  cases hxy
  · refine'
      ten_one_a n k l γ δ hl₀ hk₈ h₁₀₂ hγ hγu hδ hlk hk9l h5lk χ hχ _ x hx hml hγ'_le_γ hγ' hxy
    refine' hm.trans_le' (mul_le_mul_of_nonneg_right (exp_le_exp.2 _) (Nat.cast_nonneg _))
    simp only [neg_mul, one_div, le_neg_add_iff_add_le, add_right_neg, inv_nonneg, zero_le_bit0]
    norm_num1
  clear h₁₀₂
  exact ten_one_b n k l γ δ hl₀ hk₈ h₉₁ hγu hδ hlk hk9l h5lk χ hχ hm x hx hml hγ' hxy

-- actually `f` only needs to depend on a constant lower bound on `γ`, but oh well
theorem ten_one_true (γ : ℝ) (hγu : γ ≤ 1 / 5) :
    ∃ f : ℕ → ℝ,
      (f =o[atTop] fun x => (x : ℝ)) ∧
        ∀ k l : ℕ,
          γ = l / (k + l) →
            (ramseyNumber ![k, l] : ℝ) ≤ exp (-(γ / 40) * k + f k) * (k + l).choose l :=
  by
  cases' le_or_lt γ 0 with hγ₀ hγ₀
  · refine' ⟨fun _ => 1, is_o.comp_tendsto (is_o_const_id_at_top _) tendsto_nat_cast_atTop_atTop, _⟩
    rintro k l rfl
    have : (l : ℝ) / (k + l) = 0 := hγ₀.antisymm (by positivity)
    rw [div_eq_zero_iff, Nat.cast_eq_zero, ← Nat.cast_add, Nat.cast_eq_zero, add_eq_zero] at this
    have : l = 0 := this.elim id And.right
    rw [this, ramsey_number_pair_swap, ramsey_number_cons_zero, Nat.cast_zero,
      Nat.choose_zero_right, Nat.cast_one, mul_one]
    exact (exp_pos _).le
  have := ten_one_precise γ hγ₀
  rw [eventually_at_top] at this
  obtain ⟨L, hL⟩ := this
  replace hL := fun l hl k hγ => hL l hl k γ (γ / 40) hγ le_rfl hγu rfl
  have : ∀ k l : ℕ, γ = l / (k + l) → 0 < k ∧ 0 < l :=
    by
    rintro k l rfl
    simp only [pos_iff_ne_zero]
    have : l ≠ 0 := by rintro rfl; simpa using hγ₀
    refine' ⟨_, this⟩
    rintro rfl
    rw [Nat.cast_zero, zero_add, div_self] at hγu
    · norm_num at hγu
    · positivity
  have : ∀ k l : ℕ, γ = l / (k + l) → (⌈(L : ℝ) * ((1 - γ) / γ)⌉₊ ≤ k ↔ L ≤ l) :=
    by
    rintro k l hγ
    obtain ⟨hk, hl⟩ := this k l hγ
    have : (k : ℝ) + l ≠ 0 := by positivity
    rw [hγ, one_sub_div this, div_div_div_cancel_right _ this, add_sub_cancel, Nat.ceil_le,
      mul_div_assoc', div_le_iff', ← div_le_iff, mul_div_cancel, Nat.cast_le]
    · exact (Nat.cast_pos.2 hk).ne'
    · exact Nat.cast_pos.2 hk
    · exact Nat.cast_pos.2 hl
  refine' ⟨fun k => if ⌈(L : ℝ) * ((1 - γ) / γ)⌉₊ ≤ k then 2.05 else γ / 40 * k, _, _⟩
  · refine'
      is_o.congr' (is_o.comp_tendsto (is_o_const_id_at_top 2.05) tendsto_nat_cast_atTop_atTop) _
        eventually_eq.rfl
    filter_upwards [eventually_ge_at_top ⌈(L : ℝ) * ((1 - γ) / γ)⌉₊] with k hk
    rw [if_pos hk]
  intro k l hγ
  split_ifs with h
  · rw [this k l hγ] at h
    exact hL l h k hγ
  rw [neg_mul, neg_add_eq_sub, sub_self, Real.exp_zero, one_mul, Nat.cast_le, ← Nat.choose_symm_add]
  exact ramsey_number_le_choose'

end SimpleGraph

