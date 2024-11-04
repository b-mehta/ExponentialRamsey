/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Section4
import Prereq.GraphProbability
import Algebra.Order.Chebyshev

/-!
# Section 5
-/


open Real

theorem hMul_log_two_le_log_one_add {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1) : ε * log 2 ≤ log (1 + ε) :=
  by
  rw [le_log_iff_exp_le]
  swap
  · linarith
  have : 0 ≤ 1 - ε := by rwa [sub_nonneg]
  have := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ (log 2)) this hε (by simp)
  simp only [smul_eq_mul, MulZeroClass.mul_zero, zero_add, Real.exp_zero, mul_one,
    exp_log two_pos] at this
  refine' this.trans_eq _
  ring_nf

namespace SimpleGraph

open scoped ExponentialRamsey

open Filter Finset

theorem top_adjuster {α : Type*} [SemilatticeSup α] [Nonempty α] {p : α → Prop}
    (h : ∀ᶠ k : α in atTop, p k) : ∀ᶠ l : α in atTop, ∀ k : α, l ≤ k → p k :=
  by
  rw [eventually_at_top] at h ⊢
  obtain ⟨n, hn⟩ := h
  refine' ⟨n, _⟩
  rintro i (hi : n ≤ i) j hj
  exact hn j (hi.trans hj)

theorem eventually_le_floor (c : ℝ) (hc : c < 1) : ∀ᶠ k : ℝ in atTop, c * k ≤ ⌊k⌋₊ :=
  by
  cases le_or_lt c 0
  · filter_upwards [eventually_ge_at_top (0 : ℝ)] with x hx
    exact (Nat.cast_nonneg _).trans' (mul_nonpos_of_nonpos_of_nonneg h hx)
  filter_upwards [eventually_ge_at_top (1 - c)⁻¹] with x hx
  refine' (Nat.sub_one_lt_floor x).le.trans' _
  rwa [le_sub_comm, ← one_sub_mul, ← div_le_iff', one_div]
  rwa [sub_pos]

theorem ceil_eventually_le (c : ℝ) (hc : 1 < c) : ∀ᶠ k : ℝ in atTop, (⌈k⌉₊ : ℝ) ≤ c * k :=
  by
  filter_upwards [(tendsto_id.const_mul_at_top (sub_pos_of_lt hc)).eventually_ge_atTop 1,
    eventually_ge_at_top (0 : ℝ)] with x hx hx'
  refine' (Nat.ceil_lt_add_one hx').le.trans _
  rwa [id.def, sub_one_mul, le_sub_iff_add_le'] at hx

theorem isLittleO_rpow_rpow {r s : ℝ} (hrs : r < s) :
    (fun x : ℝ => x ^ r) =o[atTop] fun x => x ^ s :=
  by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have : 0 < s - r := sub_pos_of_lt hrs
  filter_upwards [eventually_gt_at_top (0 : ℝ),
    (tendsto_rpow_atTop this).eventually_ge_atTop (1 / ε)] with x hx hx'
  rwa [norm_rpow_of_nonneg hx.le, norm_rpow_of_nonneg hx.le, norm_of_nonneg hx.le, ← div_le_iff' hε,
    div_eq_mul_one_div, ← le_div_iff' (rpow_pos_of_pos hx _), ← rpow_sub hx]

theorem isLittleO_id_rpow {s : ℝ} (hrs : 1 < s) : (fun x : ℝ => x) =o[atTop] fun x => x ^ s := by
  simpa only [rpow_one] using is_o_rpow_rpow hrs

theorem isLittleO_one_rpow {s : ℝ} (hrs : 0 < s) :
    (fun x : ℝ => (1 : ℝ)) =o[atTop] fun x => x ^ s := by
  simpa only [rpow_zero] using is_o_rpow_rpow hrs

theorem one_lt_q_function_aux :
    ∀ᶠ k : ℕ in atTop,
      0.8 * (2 / (k : ℝ) ^ (-1 / 4 : ℝ) * log k) ≤ ⌊2 / (k : ℝ) ^ (-1 / 4 : ℝ) * log k⌋₊ :=
  by
  have : tendsto (fun x : ℝ => 2 * x ^ (1 / 4 : ℝ) * log x) at_top at_top :=
    by
    refine' tendsto.at_top_mul_at_top _ tendsto_log_at_top
    exact (tendsto_rpow_atTop (by norm_num)).const_mul_atTop two_pos
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_nat_cast_atTop_atTop
  have := (this.comp t).Eventually (eventually_le_floor 0.8 (by norm_num))
  filter_upwards [this] with k hk
  rw [neg_div, rpow_neg (Nat.cast_nonneg _), div_inv_eq_mul]
  exact hk

theorem ε_lt_one : ∀ᶠ k : ℕ in atTop, (k : ℝ) ^ (-1 / 4 : ℝ) < 1 :=
  by
  filter_upwards [eventually_gt_at_top 1] with k hk
  refine' rpow_lt_one_of_one_lt_of_neg (Nat.one_lt_cast.2 hk) (by norm_num)

theorem root_ε_lt_one : ∀ᶠ k : ℕ in atTop, (k : ℝ) ^ (-1 / 8 : ℝ) < 1 :=
  by
  filter_upwards [eventually_gt_at_top 1] with k hk
  refine' rpow_lt_one_of_one_lt_of_neg (Nat.one_lt_cast.2 hk) (by norm_num)

theorem one_lt_qFunction :
    ∀ᶠ k : ℕ in atTop,
      ∀ p₀ : ℝ, 0 ≤ p₀ → 1 ≤ qFunction k p₀ ⌊2 / (k : ℝ) ^ (-1 / 4 : ℝ) * log k⌋₊ :=
  by
  have hc : (1 : ℝ) < Real.log 2 * (4 / 5 * 2) :=
    by
    rw [← div_lt_iff]
    · exact log_two_gt_d9.trans_le' (by norm_num)
    norm_num
  have := ((is_o_id_rpow hc).add (is_o_one_rpow (zero_lt_one.trans hc))).def zero_lt_one
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_nat_cast_atTop_atTop
  filter_upwards [eventually_ge_at_top 1, one_lt_q_function_aux, t.eventually_ge_at_top 1,
    t.eventually this, ε_lt_one] with k hk hk' hk₁ hk₂ hε' p₀ hp₀
  --
  have hk₀' : (0 : ℝ) < k := Nat.cast_pos.2 hk
  rw [q_function]
  set ε : ℝ := (k : ℝ) ^ (-1 / 4 : ℝ)
  have hε : 0 < ε := rpow_pos_of_pos hk₀' _
  have hε₁ : ε ≤ 1 := hε'.le
  refine' le_add_of_nonneg_of_le hp₀ _
  rw [one_le_div hk₀', le_sub_iff_add_le, ← rpow_nat_cast]
  refine' (rpow_le_rpow_of_exponent_le _ hk').trans' _
  · rw [le_add_iff_nonneg_right]
    exact hε.le
  rw [rpow_def_of_pos, ← mul_assoc, ← mul_assoc, mul_comm, ← rpow_def_of_pos hk₀']
  swap
  · positivity
  have : log 2 * (4 / 5 * 2) ≤ log (1 + ε) * (4 / 5) * (2 / ε) :=
    by
    rw [mul_div_assoc' _ _ ε, le_div_iff' hε, ← mul_assoc, mul_assoc (Real.log _)]
    refine' mul_le_mul_of_nonneg_right (hMul_log_two_le_log_one_add hε.le hε₁) _
    norm_num1
  refine' (rpow_le_rpow_of_exponent_le hk₁ this).trans' _
  rwa [norm_of_nonneg, one_mul, norm_of_nonneg] at hk₂
  · exact rpow_nonneg_of_nonneg (Nat.cast_nonneg _) _
  positivity

theorem height_upper_bound :
    ∀ᶠ k : ℕ in atTop,
      ∀ p₀ : ℝ,
        0 ≤ p₀ → ∀ p : ℝ, p ≤ 1 → (height k p₀ p : ℝ) ≤ 2 / (k : ℝ) ^ (-1 / 4 : ℝ) * Real.log k :=
  by
  have : tendsto (fun k : ℝ => ⌊2 / (k : ℝ) ^ (-1 / 4 : ℝ) * Real.log k⌋₊) at_top at_top :=
    by
    refine' tendsto_nat_floor_at_top.comp _
    rw [neg_div]
    refine' tendsto.at_top_mul_at_top _ tendsto_log_at_top
    have : ∀ᶠ k : ℝ in at_top, 2 * k ^ (1 / 4 : ℝ) = 2 / k ^ (-(1 / 4) : ℝ) :=
      by
      filter_upwards [eventually_ge_at_top (0 : ℝ)] with k hk
      rw [rpow_neg hk, div_inv_eq_mul]
    refine' tendsto.congr' this _
    exact (tendsto_rpow_atTop (by norm_num)).const_mul_atTop two_pos
  have := this.comp tendsto_nat_cast_atTop_atTop
  filter_upwards [eventually_ne_at_top 0, this.eventually_ge_at_top 1, one_lt_q_function] with k hk
    hk' hk'' p₀ hp₀ p hp
  --
  rw [← Nat.le_floor_iff', height, dif_pos]
  rotate_left
  · exact hk
  · rw [← pos_iff_ne_zero]
    exact one_le_height
  refine' Nat.find_min' _ _
  exact ⟨hk', hp.trans (hk'' p₀ hp₀)⟩

open scoped BigOperators

-- #check weight
variable {V : Type*} [DecidableEq V] [Fintype V] {χ : TopEdgeLabelling V (Fin 2)}

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x y) -/
theorem five_five_aux_part_one {X Y : Finset V} :
    ∑ (x) (y) in X, (red_density χ) X Y * ((red_neighbors χ) x ∩ Y).card =
      (red_density χ) X Y ^ 2 * X.card ^ 2 * Y.card :=
  by
  simp_rw [sum_const, nsmul_eq_mul, ← mul_sum]
  suffices (red_density χ) X Y * X.card * Y.card = ∑ x : V in X, ((red_neighbors χ) x ∩ Y).card
    by
    rw [← this, sq, sq]
    linarith only
  rw [mul_right_comm, mul_assoc, col_density_comm, col_density_mul_mul]

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x y) -/
theorem five_five_aux_part_two {X Y : Finset V} :
    ∑ (x) (y) in X, ((red_neighbors χ) x ∩ (red_neighbors χ) y ∩ Y).card =
      ∑ z in Y, ((red_neighbors χ) z ∩ X).card ^ 2 :=
  by
  simp_rw [inter_comm, card_eq_sum_ones, ← @filter_mem_eq_inter _ _ Y, ← @filter_mem_eq_inter _ _ X,
    sum_filter, sq, sum_mul, mul_sum, boole_mul, ← ite_and, mem_inter, @sum_comm _ _ _ _ Y]
  refine' sum_congr rfl fun x hx => _
  refine' sum_congr rfl fun x' hx' => _
  refine' sum_congr rfl fun y hy => _
  refine' if_congr _ rfl rfl
  rw [@mem_col_neighbors_comm _ _ _ _ _ _ y]
  rw [@mem_col_neighbors_comm _ _ _ _ _ _ y]

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x y) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x y) -/
-- this proof might be possible without the empty casing from the col_density_sum variants
theorem five_five_aux {X Y : Finset V} :
    ∑ (x) (y) in X, (red_density χ) X Y * ((red_neighbors χ) x ∩ Y).card ≤
      ∑ (x) (y) in X, ((red_neighbors χ) x ∩ (red_neighbors χ) y ∩ Y).card :=
  by
  simp only [← Nat.cast_sum]
  rw [five_five_aux_part_one, five_five_aux_part_two, Nat.cast_sum]
  have :
    (∑ z in Y, ((red_neighbors χ) z ∩ X).card : ℝ) ^ 2 ≤
      (Y.card : ℝ) * ∑ z in Y, (((red_neighbors χ) z ∩ X).card : ℝ) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rcases X.eq_empty_or_nonempty with (rfl | hX)
  · simp
  rcases Y.eq_empty_or_nonempty with (rfl | hY)
  · simp
  have hY : 0 < (Y.card : ℝ) := by positivity
  rw [← div_le_iff' hY] at this
  simp only [Nat.cast_pow]
  refine' this.trans_eq' _
  rw [col_density_comm]
  rw [col_density_eq_sum, div_pow, div_mul_eq_mul_div, mul_pow, mul_div_mul_right,
    div_mul_eq_mul_div, sq (Y.card : ℝ), mul_div_mul_right _ _ hY.ne']
  positivity

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x y) -/
-- (13) observation 5.5
theorem five_five (χ : TopEdgeLabelling V (Fin 2)) (X Y : Finset V) :
    0 ≤ ∑ (x) (y) in X, pairWeight χ X Y x y :=
  by
  simp_rw [pair_weight, ← mul_sum, sum_sub_distrib]
  refine' mul_nonneg (by positivity) (sub_nonneg_of_le _)
  exact five_five_aux

theorem tendsto_nat_ceil_atTop {α : Type*} [LinearOrderedSemiring α] [FloorSemiring α] :
    Tendsto (fun x : α => ⌈x⌉₊) atTop atTop :=
  Nat.ceil_mono.tendsto_atTop_atTop fun n => ⟨n, (Nat.ceil_natCast _).ge⟩

theorem log_le_log_of_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : log x ≤ log y :=
  (log_le_log hx (hx.trans_le hxy)).2 hxy

theorem log_n_large (c : ℝ) :
    ∀ᶠ l : ℕ in atTop, ∀ k : ℕ, l ≤ k → c ≤ 1 / 128 * (l : ℝ) ^ (3 / 4 : ℝ) * Real.log k :=
  by
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_nat_cast_atTop_atTop
  have h34 : (0 : ℝ) < 3 / 4 := by norm_num
  have :=
    ((tendsto_rpow_atTop h34).atTop_mul_atTop tendsto_log_at_top).const_mul_atTop
      (show (0 : ℝ) < 1 / 128 by norm_num)
  filter_upwards [(this.comp t).eventually_ge_atTop c, t.eventually_gt_at_top (0 : ℝ)] with l hl hl'
    k hlk
  refine' hl.trans _
  dsimp
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_left (log_le_log_of_le hl' (Nat.cast_le.2 hlk)) (by positivity)

theorem five_six_aux_left_term :
    ∀ᶠ l : ℕ in atTop,
      ∀ k : ℕ,
        l ≤ k →
          (⌊exp (1 / 128 * (l : ℝ) ^ (3 / 4 : ℝ) * log k)⌋₊ : ℝ) ^ ⌈(l : ℝ) ^ (3 / 4 : ℝ)⌉₊ *
              ((k : ℝ) ^ (-1 / 8 : ℝ)) ^ ((⌈(l : ℝ) ^ (3 / 4 : ℝ)⌉₊ : ℝ) ^ 2 / 4) <
            1 / 2 :=
  by
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_nat_cast_atTop_atTop
  have h12 : (0 : ℝ) < 1 / 2 := by norm_num
  have h34 : (0 : ℝ) < 3 / 4 := by norm_num
  have h32 : (0 : ℝ) < 3 / 2 := by norm_num
  have := ((tendsto_rpow_atTop h34).comp t).Eventually (ceil_eventually_le 2 one_lt_two)
  filter_upwards [this, log_n_large 1, t.eventually_gt_at_top (1 : ℝ),
    (((tendsto_rpow_atTop h32).atTop_mul_atTop tendsto_log_at_top).comp t).eventually_gt_atTop
      (64 * log 2)] with
    l h₁ h₂ h₃ h₄ k hlk
  dsimp at h₁
  specialize h₂ k hlk
  have h₃' : (1 : ℝ) < k := h₃.trans_le (Nat.cast_le.2 hlk)
  have h₃'1 : (0 : ℝ) < k := zero_lt_one.trans h₃'
  have h'₁ : (0 : ℝ) < ⌊exp (1 / 128 * (l : ℝ) ^ (3 / 4 : ℝ) * log k)⌋₊ :=
    by
    rw [Nat.cast_pos, Nat.floor_pos]
    exact one_le_exp (h₂.trans' zero_le_one)
  rw [← rpow_mul (Nat.cast_nonneg k), ← log_lt_log_iff]
  rotate_left
  · exact mul_pos (pow_pos h'₁ _) (rpow_pos_of_pos h₃'1 _)
  · norm_num1
  rw [log_mul, log_pow, log_rpow h₃'1, mul_comm]
  rotate_left
  · exact (pow_pos h'₁ _).ne'
  · exact (rpow_pos_of_pos h₃'1 _).ne'
  refine'
    (add_le_add_right
          (mul_le_mul (log_le_log_of_le h'₁ (Nat.floor_le (exp_pos _).le)) h₁ (Nat.cast_nonneg _) _)
          _).trans_lt
      _
  · rw [log_exp]
    exact h₂.trans' zero_le_one
  rw [log_exp, neg_div, neg_mul, div_mul_div_comm, one_mul, mul_right_comm, ← add_mul,
    mul_mul_mul_comm, ← rpow_add (zero_lt_one.trans h₃), mul_comm (1 / 128 : ℝ), ←
    div_eq_mul_one_div, div_eq_mul_one_div (_ ^ 2 : ℝ)]
  have : (l : ℝ) ^ (2 * (3 / 4) : ℝ) ≤ (⌈(l : ℝ) ^ (3 / 4 : ℝ)⌉₊ : ℝ) ^ 2 := by
    calc
      _ = (l : ℝ) ^ (3 / 4 * 2 : ℝ) := by rw [mul_comm]
      _ = ((l : ℝ) ^ (3 / 4 : ℝ)) ^ (2 : ℝ) := (rpow_mul (Nat.cast_nonneg _) _ _)
      _ = ((l : ℝ) ^ (3 / 4 : ℝ)) ^ (2 : ℕ) := (rpow_two _)
      _ ≤ (⌈(l : ℝ) ^ (3 / 4 : ℝ)⌉₊ : ℝ) ^ 2 :=
        pow_le_pow_of_le_left (by positivity) (Nat.le_ceil _) _
  refine'
    (mul_le_mul_of_nonneg_right
          (add_le_add_left (neg_le_neg (mul_le_mul_of_nonneg_right this (by norm_num))) _)
          (log_nonneg h₃'.le)).trans_lt
      _
  rw [← two_mul, mul_comm (_ / _), ← sub_eq_add_neg, ← mul_sub, mul_right_comm]
  norm_num1
  rw [one_div (2 : ℝ), mul_neg, log_inv, neg_lt_neg_iff, ← div_eq_mul_one_div, lt_div_iff']
  swap
  · norm_num
  exact
    (mul_le_mul_of_nonneg_left (log_le_log_of_le (zero_lt_one.trans h₃) (Nat.cast_le.2 hlk))
          (by positivity)).trans_lt'
      h₄

theorem five_six_aux_right_term_aux : ∀ᶠ k : ℝ in atTop, 1 ≤ 32 * k ^ (1 / 8 : ℝ) - log k :=
  by
  have h8 : (0 : ℝ) < 1 / 8 := by norm_num
  filter_upwards [(isLittleO_log_rpow_atTop h8).def zero_lt_one,
    (tendsto_rpow_atTop h8).eventually_ge_atTop 1, tendsto_log_at_top.eventually_ge_at_top (0 : ℝ),
    eventually_ge_at_top (0 : ℝ)] with x hx hx' hxl hx₀
  rw [norm_of_nonneg hxl, norm_of_nonneg (rpow_nonneg_of_nonneg hx₀ _), one_mul] at hx
  linarith only [hx, hx']

theorem five_six_aux_right_term :
    ∀ᶠ l : ℕ in atTop,
      ∀ k : ℕ,
        l ≤ k →
          (⌊exp (1 / 128 * (l : ℝ) ^ (3 / 4 : ℝ) * log k)⌋₊ : ℝ) ^ k *
              exp (-k ^ (-1 / 8 : ℝ) * k ^ 2 / 4) <
            1 / 2 :=
  by
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_nat_cast_atTop_atTop
  have h : (0 : ℝ) < 3 / 4 + 1 := by norm_num1
  filter_upwards [eventually_gt_at_top 1, log_n_large 1,
    top_adjuster (((tendsto_rpow_atTop h).comp t).eventually_gt_atTop (128 * log 2)),
    top_adjuster (t.eventually five_six_aux_right_term_aux)] with l h₁ h₂ h₃ h₄ k hlk
  --
  specialize h₂ k hlk
  have h'₁ : (0 : ℝ) < ⌊exp (1 / 128 * (l : ℝ) ^ (3 / 4 : ℝ) * log k)⌋₊ :=
    by
    rw [Nat.cast_pos, Nat.floor_pos]
    exact one_le_exp (h₂.trans' zero_le_one)
  rw [neg_mul, ← rpow_two, ← rpow_add, ← log_lt_log_iff (mul_pos (pow_pos h'₁ _) (exp_pos _)),
    log_mul (pow_ne_zero _ h'₁.ne') (exp_pos _).ne', log_exp, log_pow]
  rotate_left
  · norm_num1
  · rwa [Nat.cast_pos]
    exact zero_lt_one.trans (h₁.trans_le hlk)
  refine'
    (add_le_add_right
          (mul_le_mul_of_nonneg_left (log_le_log_of_le h'₁ (Nat.floor_le (exp_pos _).le))
            (Nat.cast_nonneg _))
          _).trans_lt
      _
  rw [log_exp, mul_right_comm, ← mul_assoc]
  refine'
    (add_le_add_right
          (mul_le_mul_of_nonneg_left (rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.2 hlk) _)
            (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg _ _)))
          _).trans_lt
      _
  · norm_num1
  · norm_num1
  · exact log_nonneg (Nat.one_le_cast.2 (h₁.le.trans hlk))
  rw [mul_comm, ← mul_assoc, ← rpow_add_one, neg_div, ← sub_eq_add_neg, ← mul_assoc]
  swap
  · rw [Nat.cast_ne_zero]
    linarith only [h₁.le.trans hlk]
  have h :
    (k : ℝ) ^ (-1 / 8 + 2 : ℝ) / 4 = k ^ (3 / 4 + 1 : ℝ) * (1 / 128) * (32 * k ^ (1 / 8 : ℝ)) :=
    by
    rw [← div_eq_mul_one_div, div_eq_mul_one_div _ (4 : ℝ), div_mul_eq_mul_div, mul_left_comm, ←
      rpow_add, ← div_mul_eq_mul_div, mul_comm]
    · norm_num1; rfl
    rwa [Nat.cast_pos]
    exact zero_lt_one.trans (h₁.trans_le hlk)
  rw [h, ← mul_sub, one_div (2 : ℝ), log_inv, lt_neg, ← mul_neg, neg_sub, mul_one_div,
    div_mul_eq_mul_div, lt_div_iff']
  swap; · norm_num1
  refine' (h₃ _ hlk).trans_le _
  exact le_mul_of_one_le_right (rpow_nonneg_of_nonneg (Nat.cast_nonneg _) _) (h₄ _ hlk)

theorem five_six_aux_part_one :
    ∃ c : ℝ,
      0 < c ∧
        ∀ᶠ l : ℕ in atTop,
          ∀ k : ℕ,
            l ≤ k →
              exp (c * l ^ (3 / 4 : ℝ) * log k) ≤ ramseyNumber ![k, ⌈(l : ℝ) ^ (3 / 4 : ℝ)⌉₊] :=
  by
  refine' ⟨1 / 128, by norm_num, _⟩
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_nat_cast_atTop_atTop
  have h34 : (0 : ℝ) < 3 / 4 := by norm_num
  have := (tendsto_nat_ceil_at_top.comp (tendsto_rpow_atTop h34)).comp t
  filter_upwards [top_adjuster (t.eventually_gt_at_top 0), eventually_ge_at_top 2,
    this.eventually_ge_at_top 2, five_six_aux_left_term, five_six_aux_right_term,
    top_adjuster root_ε_lt_one] with l hl₁ℕ hl₂ℕ hl₃ hf' hf'' hε k hlk
  refine' le_of_lt _
  rw [← Nat.floor_lt (exp_pos _).le]
  specialize hf' k hlk
  specialize hf'' k hlk
  set p : ℝ := k ^ (-1 / 8 : ℝ)
  have hp₀ : 0 < p := by
    refine' rpow_pos_of_pos _ _
    exact hl₁ℕ k hlk
  have hp₁ : p < 1 := hε k hlk
  rw [ramsey_number_pair_swap]
  refine' basic_off_diagonal_ramsey_bound hp₀ hp₁ hl₃ (hl₂ℕ.trans hlk) _
  exact (add_lt_add hf' hf'').trans_eq (by norm_num)

theorem five_six :
    ∀ᶠ l : ℕ in atTop,
      ∀ k : ℕ,
        l ≤ k →
          k ^ 6 * ramseyNumber ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊] ≤
            ramseyNumber ![k, ⌈(l : ℝ) ^ (3 / 4 : ℝ)⌉₊] :=
  by
  obtain ⟨c, hc, hf⟩ := five_six_aux_part_one
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_nat_cast_atTop_atTop
  have h23 : (0 : ℝ) < 2 / 3 := by norm_num
  have h34 : (0 : ℝ) < 3 / 4 := by norm_num
  have h2334 : (2 / 3 : ℝ) < 3 / 4 := by norm_num
  have hc6 : 0 < c / 6 := by positivity
  have := ((is_o_one_rpow h34).add (is_o_rpow_rpow h2334)).def hc6
  filter_upwards [hf, top_adjuster (t.eventually_gt_at_top 0),
    top_adjuster ((tendsto_log_at_top.comp t).eventually_ge_atTop 0),
    ((tendsto_rpow_atTop h23).comp t).Eventually (ceil_eventually_le 6 (by norm_num)),
    t.eventually (((is_o_one_rpow h34).add (is_o_rpow_rpow h2334)).def hc6)] with l hl hl₀ hll₀ hl'
    hl₁ k hlk
  specialize hl k hlk
  rw [ramsey_number_pair_swap]
  refine' (Nat.mul_le_mul_left _ ramsey_number_le_right_pow_left').trans _
  rw [← @Nat.cast_le ℝ, ← pow_add, Nat.cast_pow]
  refine' hl.trans' _
  rw [← log_le_iff_le_exp (pow_pos (hl₀ _ hlk) _), log_pow, Nat.cast_add, Nat.cast_bit0,
    Nat.cast_bit1, Nat.cast_one]
  refine' mul_le_mul_of_nonneg_right _ (hll₀ _ hlk)
  refine' (add_le_add_left hl' _).trans _
  rw [← mul_one_add, ← le_div_iff', ← div_mul_eq_mul_div]
  swap
  · norm_num1
  refine' ((le_norm_self _).trans hl₁).trans_eq _
  rw [norm_of_nonneg]
  exact rpow_nonneg_of_nonneg (Nat.cast_nonneg _) _

theorem abs_pairWeight_le_one {X Y : Finset V} {x y : V} : |pairWeight χ X Y x y| ≤ 1 :=
  by
  rw [pair_weight, abs_mul, abs_inv]
  cases Nat.eq_zero_or_pos Y.card
  · rw [h, Nat.cast_zero, abs_zero, inv_zero, MulZeroClass.zero_mul]
    exact zero_le_one
  rw [Nat.abs_cast, inv_mul_le_iff, mul_one]
  swap
  · rwa [Nat.cast_pos]
  have hr₀ : 0 ≤ (red_density χ) X Y := col_density_nonneg
  have hr₁ : (red_density χ) X Y ≤ 1 := col_density_le_one
  have :
    Set.uIcc ((red_density χ) X Y * ((red_neighbors χ) x ∩ Y).card)
        ((red_neighbors χ) x ∩ (red_neighbors χ) y ∩ Y).card ⊆
      Set.uIcc 0 Y.card :=
    by
    rw [Set.uIcc_subset_uIcc_iff_mem, Set.uIcc_of_le, Set.mem_Icc, Set.mem_Icc, and_assoc']
    swap
    · exact Nat.cast_nonneg _
    exact
      ⟨by positivity,
        mul_le_of_le_one_of_le' hr₁ (Nat.cast_le.2 (card_le_of_subset (inter_subset_right _ _))) hr₀
          (Nat.cast_nonneg _),
        Nat.cast_nonneg _, Nat.cast_le.2 (card_le_of_subset (inter_subset_right _ _))⟩
  refine' (Set.abs_sub_le_of_uIcc_subset_uIcc this).trans _
  simp

theorem sum_pairWeight_eq {X Y : Finset V} (y : V) (hy : y ∈ X) :
    ∑ x in X, pairWeight χ X Y y x = weight χ X Y y + pairWeight χ X Y y y := by
  rw [weight, sum_erase_add _ _ hy]

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x y) -/
theorem double_sum_pairWeight_eq {X Y : Finset V} :
    ∑ (x) (y) in X, pairWeight χ X Y x y = ∑ y in X, (weight χ X Y y + pairWeight χ X Y y y) :=
  sum_congr rfl sum_pairWeight_eq

theorem sum_pairWeight_le {X Y : Finset V} (y : V) (hy : y ∈ X) :
    weight χ X Y y + pairWeight χ X Y y y ≤ X.card :=
  by
  rw [← sum_pair_weight_eq _ hy]
  refine' le_of_abs_le ((abs_sum_le_sum_abs _ _).trans _)
  refine' (sum_le_card_nsmul _ _ 1 _).trans_eq (Nat.smul_one_eq_coe _)
  intro x hx
  exact abs_pair_weight_le_one

theorem five_four_aux (μ : ℝ) (k l : ℕ) (ini : BookConfig χ) (i : ℕ)
    (hi : i ∈ redOrDensitySteps μ k l ini) :
    (0 : ℝ) ≤
      ramseyNumber ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊] * (algorithm μ k l ini i).X.card +
        ((algorithm μ k l ini i).X.card - ramseyNumber ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊]) *
          (weight χ (algorithm μ k l ini i).X (algorithm μ k l ini i).y (getX hi) + 1) :=
  by
  set C := algorithm μ k l ini i
  let m := ramsey_number ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊]
  have hi' := hi
  simp only [red_or_density_steps, mem_filter, mem_range] at hi'
  change (0 : ℝ) ≤ m * C.X.card + (C.X.card - m) * (weight χ C.X C.Y (get_x hi) + 1)
  refine' (five_five χ C.X C.Y).trans _
  rw [double_sum_pair_weight_eq]
  rw [book_config.num_big_blues] at hi'
  have : C.X.card - m ≤ (book_config.central_vertices μ C).card :=
    by
    rw [tsub_le_iff_right, book_config.central_vertices]
    refine' (add_le_add_left hi'.2.2.le _).trans' ((card_union_le _ _).trans' (card_le_of_subset _))
    rw [← filter_or]
    simp (config := { contextual := true }) only [Finset.subset_iff, mem_filter, true_and_iff]
    intro x hx
    exact le_total _ _
  obtain ⟨nei, Bnei, neicard⟩ := exists_smaller_set _ _ this
  have : ramsey_number ![k, ⌈(l : ℝ) ^ (3 / 4 : ℝ)⌉₊] < C.X.card :=
    ramsey_number_lt_of_lt_final_step hi'.1
  have hm : m ≤ C.X.card := by
    refine' this.le.trans' _
    refine' ramsey_number.mono_two le_rfl _
    refine' Nat.ceil_mono _
    rcases Nat.eq_zero_or_pos l with (rfl | hl)
    · rw [Nat.cast_zero, zero_rpow, zero_rpow] <;> norm_num1
    refine' rpow_le_rpow_of_exponent_le _ (by norm_num1)
    rwa [Nat.one_le_cast, Nat.succ_le_iff]
  have : book_config.central_vertices μ C ⊆ C.X := filter_subset _ _
  have h : (C.X \ nei).card = m := by
    rw [card_sdiff (Bnei.trans this), neicard, Nat.sub_sub_self hm]
  rw [← sum_sdiff (Bnei.trans this), ← nsmul_eq_mul, ← Nat.cast_sub hm, ← neicard, ← h, ←
    nsmul_eq_mul]
  refine' add_le_add (sum_le_card_nsmul _ _ _ _) (sum_le_card_nsmul _ _ _ _)
  · intro x hx
    exact sum_pair_weight_le x (sdiff_subset _ _ hx)
  intro x hx
  refine' add_le_add _ (le_of_abs_le abs_pair_weight_le_one)
  refine' book_config.get_central_vertex_max _ _ _ _ _
  exact Bnei hx

theorem five_four_end : ∀ᶠ k : ℝ in atTop, 1 / (k ^ 6 - 1) + 1 / k ^ 6 ≤ 1 / k ^ 5 :=
  by
  filter_upwards [eventually_ge_at_top (3 : ℝ)] with k hk₁
  rw [← add_halves' (1 / k ^ 5), div_div]
  have h1 : 0 < k ^ 5 * 2 := by positivity
  suffices h2 : k ^ 5 * 2 ≤ k ^ 6 - 1
  · refine' add_le_add (one_div_le_one_div_of_le h1 h2) (one_div_le_one_div_of_le h1 (h2.trans _))
    simp
  rw [pow_succ' _ 5, le_sub_comm, ← mul_sub]
  exact
    one_le_mul_of_one_le_of_one_le (one_le_pow_of_one_le (hk₁.trans' (by norm_num)) _)
      (by linarith only [hk₁])

theorem five_four :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ : ℝ,
            ∀ n : ℕ,
              ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                ∀ ini : BookConfig χ,
                  ∀ i : ℕ,
                    ∀ hi : i ∈ redOrDensitySteps μ k l ini,
                      -((algorithm μ k l ini i).X.card : ℝ) / k ^ 5 ≤
                        weight χ (algorithm μ k l ini i).X (algorithm μ k l ini i).y (getX hi) :=
  by
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_nat_cast_atTop_atTop
  have h23 : (0 : ℝ) < 2 / 3 := by norm_num
  have := (tendsto_nat_ceil_at_top.comp (tendsto_rpow_atTop h23)).comp t
  filter_upwards [five_six, this.eventually_ge_at_top 1, top_adjuster (eventually_gt_at_top 1),
    top_adjuster (t.eventually five_four_end)] with l hl hl' hl₂ hl₃ k hlk μ n χ ini i hi
  specialize hl₂ k hlk
  specialize hl₃ k hlk
  have hi' := hi
  rw [red_or_density_steps, mem_filter, mem_range] at hi'
  set C := algorithm μ k l ini i
  change -(C.X.card : ℝ) / k ^ 5 ≤ weight χ C.X C.Y (get_x hi)
  let m := ramsey_number ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊]
  have h₅₄ : (0 : ℝ) ≤ m * C.X.card + (C.X.card - m) * (weight χ C.X C.Y _ + 1) :=
    five_four_aux μ k l ini i hi
  have hm : 1 ≤ m := by
    refine' ramsey_number_ge_min _ _
    simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      hl₂.le, true_and_iff, hl']
  have hX : k ^ 6 * m ≤ C.X.card := (hl k hlk).trans (ramsey_number_lt_of_lt_final_step hi'.1).le
  have h : (k ^ 6 - 1 : ℝ) * m ≤ (C.X.card : ℝ) - m :=
    by
    rw [sub_one_mul, sub_le_sub_iff_right]
    exact_mod_cast hX
  have c : (k ^ 6 : ℝ) ≤ C.X.card :=
    by
    rw [← Nat.cast_pow, Nat.cast_le]
    exact hX.trans' (Nat.le_mul_of_pos_right hm)
  have b' : (m : ℝ) < C.X.card := by
    rw [Nat.cast_lt]
    refine' hX.trans_lt' _
    refine' lt_mul_left hm _
    exact one_lt_pow hl₂ (by norm_num)
  have b : (0 : ℝ) < C.X.card - m := by rwa [sub_pos]
  have : (0 : ℝ) < C.X.card := by
    refine' b.trans_le _
    simp only [sub_le_self_iff, Nat.cast_nonneg]
  rw [neg_div, div_eq_mul_one_div, ← mul_neg, ← le_div_iff' this]
  have : -(m / (C.X.card - m) + 1 / C.X.card : ℝ) ≤ weight χ C.X C.Y (get_x hi) / C.X.card :=
    by
    rw [neg_le_iff_add_nonneg', add_assoc, div_add_div_same, add_comm (1 : ℝ),
      div_add_div _ _ b.ne' this.ne']
    exact div_nonneg h₅₄ (mul_nonneg b.le (Nat.cast_nonneg _))
  refine' this.trans' _
  rw [neg_le_neg_iff]
  refine' (add_le_add (div_le_div_of_le_left _ _ h) (div_le_div_of_le_left zero_le_one _ c)).trans _
  · exact Nat.cast_nonneg _
  · refine' mul_pos (sub_pos_of_lt (one_lt_pow (Nat.one_lt_cast.2 hl₂) (by norm_num1))) _
    rwa [Nat.cast_pos]
  · refine' pow_pos _ _
    rwa [Nat.cast_pos]
    exact hl₂.le
  rw [mul_comm, ← div_div, div_self]
  swap
  · rw [Nat.cast_ne_zero, ← pos_iff_ne_zero]
    exact hm
  exact hl₃

theorem five_seven_aux {k : ℕ} {p₀ p : ℝ} :
    αFunction k (height k p₀ p) =
      (k : ℝ) ^ (-1 / 4 : ℝ) * (qFunction k p₀ (height k p₀ p - 1) - qFunction k p₀ 0 + 1 / k) :=
  by
  rw [α_function, q_function, q_function, pow_zero, sub_self, zero_div, add_zero, add_sub_cancel', ←
    add_div, sub_add_cancel, mul_div_assoc]

theorem height_spec {k : ℕ} {p₀ p : ℝ} (hk : k ≠ 0) : p ≤ qFunction k p₀ (height k p₀ p) :=
  by
  rw [height, dif_pos hk]
  exact (Nat.find_spec (q_function_above _ _ hk)).2

theorem height_min {k h : ℕ} {p₀ p : ℝ} (hk : k ≠ 0) (hh : h ≠ 0) :
    p ≤ qFunction k p₀ h → height k p₀ p ≤ h :=
  by
  intro h'
  rw [height, dif_pos hk]
  refine' Nat.find_min' (q_function_above _ _ hk) ⟨hh.bot_lt, h'⟩

theorem five_seven_left {k : ℕ} {p₀ p : ℝ} :
    (k : ℝ) ^ (-1 / 4 : ℝ) / k ≤ αFunction k (height k p₀ p) :=
  by
  rw [five_seven_aux, div_eq_mul_one_div]
  refine' mul_le_mul_of_nonneg_left _ (rpow_nonneg_of_nonneg (Nat.cast_nonneg _) _)
  rw [le_add_iff_nonneg_left, sub_nonneg]
  refine' q_increasing _
  exact Nat.zero_le _

theorem α_one {k : ℕ} : αFunction k 1 = (k : ℝ) ^ (-1 / 4 : ℝ) / k := by
  rw [α_function, Nat.sub_self, pow_zero, mul_one]

theorem q_height_lt_p {k : ℕ} {p₀ p : ℝ} (h : 1 < height k p₀ p) :
    qFunction k p₀ (height k p₀ p - 1) < p :=
  by
  have : k ≠ 0 := by
    replace h := h.ne'
    rw [height] at h
    simp only [Ne.def, dite_eq_right_iff, Classical.not_forall] at h
    obtain ⟨hh, -⟩ := h
    exact hh
  by_contra' z
  have := height_min this _ z
  · rw [← not_lt] at this
    exact this (Nat.sub_lt one_le_height zero_lt_one)
  simpa using h

theorem five_seven_right {k : ℕ} {p₀ p : ℝ} (h : qFunction k p₀ 0 ≤ p) :
    αFunction k (height k p₀ p) ≤ (k : ℝ) ^ (-1 / 4 : ℝ) * (p - qFunction k p₀ 0 + 1 / k) :=
  by
  rw [five_seven_aux]
  refine' mul_le_mul_of_nonneg_left _ (rpow_nonneg_of_nonneg (Nat.cast_nonneg _) _)
  simp only [add_le_add_iff_right, sub_le_sub_iff_right]
  cases' lt_or_eq_of_le (@one_le_height k p₀ p) with h₁ h₁
  · exact (q_height_lt_p h₁).le
  rwa [h₁, Nat.sub_self]

theorem five_seven_extra {k : ℕ} {p₀ p : ℝ} (h' : p ≤ qFunction k p₀ 1) : height k p₀ p = 1 :=
  by
  rw [height]
  split_ifs
  · rw [Nat.find_eq_iff]
    simp [h']
  rfl

-- WARNING: the hypothesis 1 / k ≤ ini.p should be seen as setting an absolute lower bound on p₀,
-- and k and ini both depend on it, with 1 / k ≤ it ≤ ini.p
theorem five_eight {μ : ℝ} {k l : ℕ} {ini : BookConfig χ} (h : 1 / (k : ℝ) ≤ ini.p) {i : ℕ}
    (hi : i ∈ degreeSteps μ k l ini) (x : V) (hx : x ∈ (algorithm μ k l ini (i + 1)).X) :
    (1 - (k : ℝ) ^ (-1 / 8 : ℝ)) * (algorithm μ k l ini i).p *
        (algorithm μ k l ini (i + 1)).y.card ≤
      ((red_neighbors χ) x ∩ (algorithm μ k l ini (i + 1)).y).card :=
  by
  set C := algorithm μ k l ini i
  set ε := (k : ℝ) ^ (-1 / 4 : ℝ)
  rw [degree_regularisation_applied hi, book_config.degree_regularisation_step_Y]
  rw [degree_regularisation_applied hi, book_config.degree_regularisation_step_X, mem_filter] at hx
  rw [degree_steps, mem_filter, mem_range] at hi
  change (1 - (k : ℝ) ^ (-1 / 8 : ℝ)) * C.p * C.Y.card ≤ ((red_neighbors χ) x ∩ C.Y).card
  change
    x ∈ C.X ∧
      (C.p - _ * α_function k (height k ini.p C.p)) * (C.Y.card : ℝ) ≤
        ((red_neighbors χ) x ∩ C.Y).card at
    hx
  have : 1 / (k : ℝ) < C.p := one_div_k_lt_p_of_lt_final_step hi.1
  refine' hx.2.trans' (mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _))
  rw [one_sub_mul, sub_le_sub_iff_left]
  cases' le_total C.p (q_function k ini.p 0) with h' h'
  · rw [five_seven_extra, α_one, mul_div_assoc', ← rpow_add' (Nat.cast_nonneg _),
      div_eq_mul_one_div]
    · refine'
        (mul_le_mul_of_nonneg_left this.le (rpow_nonneg_of_nonneg (Nat.cast_nonneg _) _)).trans_eq _
      norm_num
    · norm_num
    exact h'.trans (q_increasing zero_le_one)
  refine'
    (mul_le_mul_of_nonneg_left (five_seven_right h')
          (rpow_nonneg_of_nonneg (Nat.cast_nonneg _) _)).trans
      _
  rw [← mul_assoc, ← rpow_add' (Nat.cast_nonneg _)]
  swap
  · norm_num1
  refine' mul_le_mul _ _ _ _
  · refine' le_of_eq _
    norm_num
  · rw [q_function_zero, sub_add, sub_le_self_iff, sub_nonneg]
    exact h
  · refine' add_nonneg _ _
    · rwa [sub_nonneg]
    · positivity
  · positivity

theorem five_eight_weak {μ : ℝ} {k l : ℕ} {ini : BookConfig χ} (h : 1 / (k : ℝ) ≤ ini.p) {i : ℕ}
    (hi : i ∈ degreeSteps μ k l ini) (x : V) (hx : x ∈ (algorithm μ k l ini (i + 1)).X) :
    (1 - (k : ℝ) ^ (-1 / 8 : ℝ)) * (1 / k) * (algorithm μ k l ini (i + 1)).y.card ≤
      ((red_neighbors χ) x ∩ (algorithm μ k l ini (i + 1)).y).card :=
  by
  rcases eq_or_ne k 0 with (rfl | hk)
  · simp
  refine' (five_eight h hi x hx).trans' _
  refine' mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  refine' mul_le_mul_of_nonneg_left _ _
  · rw [degree_steps, mem_filter, mem_range] at hi
    exact (one_div_k_lt_p_of_lt_final_step hi.1).le
  rw [sub_nonneg]
  refine' rpow_le_one_of_one_le_of_nonpos _ (by norm_num)
  rwa [Nat.one_le_cast, Nat.succ_le_iff, pos_iff_ne_zero]

theorem five_eight_weaker (p₀l : ℝ) (hp₀l : 0 < p₀l) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ,
            ∀ n : ℕ,
              ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                ∀ ini : BookConfig χ,
                  p₀l ≤ ini.p →
                    ∀ i : ℕ,
                      ∀ x : Fin n,
                        i ∈ degreeSteps μ k l ini →
                          x ∈ (algorithm μ k l ini (i + 1)).X →
                            (1 : ℝ) / (2 * k) * (algorithm μ k l ini (i + 1)).y.card ≤
                              ((red_neighbors χ) x ∩ (algorithm μ k l ini (i + 1)).y).card :=
  by
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_nat_cast_atTop_atTop
  have := tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 8 by norm_num)
  have := eventually_le_of_tendsto_lt (show (0 : ℝ) < 1 - 2⁻¹ by norm_num) this
  filter_upwards [top_adjuster (t.eventually_ge_at_top p₀l⁻¹),
    top_adjuster (t.eventually this)] with l hl hl₂ k hlk μ n χ ini hini i x hi hx
  specialize hl k hlk
  specialize hl₂ k hlk
  refine' (five_eight_weak _ hi x hx).trans' _
  · refine' hini.trans' _
    rw [one_div]
    exact inv_le_of_inv_le hp₀l hl
  refine' mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [one_div, mul_inv, one_div]
  refine' mul_le_mul_of_nonneg_right _ (by positivity)
  rw [le_sub_comm, neg_div]
  exact hl₂

theorem five_eight_weaker' (p₀l : ℝ) (hp₀l : 0 < p₀l) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ,
            ∀ n : ℕ,
              ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                ∀ ini : BookConfig χ,
                  p₀l ≤ ini.p →
                    ∀ i : ℕ,
                      ∀ x : Fin n,
                        i ∈ redOrDensitySteps μ k l ini →
                          x ∈ (algorithm μ k l ini i).X →
                            (1 : ℝ) / (2 * k) * (algorithm μ k l ini i).y.card ≤
                              ((red_neighbors χ) x ∩ (algorithm μ k l ini i).y).card :=
  by
  filter_upwards [five_eight_weaker p₀l hp₀l] with l hl k hlk μ n χ ini hini i x hi hx
  rw [red_or_density_steps, mem_filter, ← Nat.odd_iff_not_even, mem_range] at hi
  rcases hi.2.1 with ⟨j, rfl⟩
  refine' hl k hlk μ n χ ini hini (2 * j) x _ hx
  rw [degree_steps, mem_filter, mem_range]
  exact ⟨hi.1.trans_le' (Nat.le_succ _), by simp⟩

theorem q_height_le_two {k : ℕ} {p₀ p : ℝ} (hp₀₁ : p₀ ≤ 1) (hp₂ : p ≤ 2) :
    qFunction k p₀ (height k p₀ p - 1) ≤ 2 :=
  by
  cases' eq_or_lt_of_le (@one_le_height k p₀ p) with h₁ h₁
  · rw [← h₁, Nat.sub_self, q_function_zero]
    exact hp₀₁.trans one_le_two
  exact (q_height_lt_p h₁).le.trans hp₂

theorem α_le_one {k : ℕ} {p₀ p : ℝ} (hp₀₁ : p₀ ≤ 1) (h : 1 / (k : ℝ) ≤ p₀) (hk : 2 ^ 4 ≤ k)
    (hp : p ≤ 2) : αFunction k (height k p₀ p) ≤ 1 :=
  by
  rcases eq_or_ne k 0 with (rfl | hk₀)
  · rw [α_function]
    simp only [CharP.cast_eq_zero, div_zero, zero_le_one]
  rw [five_seven_aux, q_function_zero, mul_comm, ← le_div_iff, neg_div,
    rpow_neg (Nat.cast_nonneg _), one_div _⁻¹, inv_inv]
  swap
  · positivity
  rw [sub_add]
  refine' (sub_le_sub_right (q_height_le_two hp₀₁ hp) _).trans _
  refine' (sub_le_self _ (sub_nonneg_of_le h)).trans _
  refine' (rpow_le_rpow (by norm_num1) (Nat.cast_le.2 hk) (by norm_num)).trans' _
  rw [Nat.cast_pow, ← rpow_nat_cast, ← rpow_mul] <;> norm_num

variable {k l : ℕ} {ini : BookConfig χ} {i : ℕ}

theorem p_pos {μ : ℝ} (hi : i < finalStep μ k l ini) : 0 < (algorithm μ k l ini i).p :=
  by
  refine' (one_div_k_lt_p_of_lt_final_step hi).trans_le' _
  positivity

theorem x_nonempty {μ : ℝ} (hi : i < finalStep μ k l ini) : (algorithm μ k l ini i).X.Nonempty :=
  by
  refine' nonempty_of_ne_empty _
  intro h
  refine' (p_pos hi).ne' _
  rw [book_config.p, h, col_density_empty_left]

theorem y_nonempty {μ : ℝ} (hi : i < finalStep μ k l ini) : (algorithm μ k l ini i).y.Nonempty :=
  by
  refine' nonempty_of_ne_empty _
  intro h
  refine' (p_pos hi).ne' _
  rw [book_config.p, h, col_density_empty_right]

-- WARNING: the hypothesis 1 / k ≤ ini.p should be seen as setting an absolute lower bound on p₀,
-- and k and ini both depend on it, with 1 / k ≤ it ≤ ini.p
theorem red_neighbors_y_nonempty {μ : ℝ} (h : 1 / (k : ℝ) ≤ ini.p) (hk : 1 < k)
    (hi : i ∈ degreeSteps μ k l ini) (x : V) (hx : x ∈ (algorithm μ k l ini (i + 1)).X) :
    ((red_neighbors χ) x ∩ (algorithm μ k l ini (i + 1)).y).Nonempty :=
  by
  rw [← card_pos, ← @Nat.cast_pos ℝ]
  have : i < final_step μ k l ini :=
    by
    rw [degree_steps, mem_filter, mem_range] at hi
    exact hi.1
  refine' (five_eight h hi x hx).trans_lt' _
  refine' mul_pos (mul_pos _ (p_pos this)) _
  · rw [sub_pos]
    refine' rpow_lt_one_of_one_lt_of_neg _ _
    · rwa [Nat.one_lt_cast]
    norm_num1
  rw [Nat.cast_pos, card_pos, degree_regularisation_applied hi,
    book_config.degree_regularisation_step_Y]
  exact Y_nonempty this

theorem red_neighbors_y_nonempty' {μ : ℝ} (h : 1 / (k : ℝ) ≤ ini.p) (hk : 1 < k)
    (hi : i ∈ redOrDensitySteps μ k l ini) (x : V) (hx : x ∈ (algorithm μ k l ini i).X) :
    ((red_neighbors χ) x ∩ (algorithm μ k l ini i).y).Nonempty :=
  by
  rw [red_or_density_steps, mem_filter, ← Nat.odd_iff_not_even, mem_range] at hi
  rcases hi.2.1 with ⟨j, rfl⟩
  refine' red_neighbors_Y_nonempty h hk _ x hx
  rw [degree_steps, mem_filter, mem_range]
  exact ⟨hi.1.trans_le' (Nat.le_succ _), by simp⟩

theorem red_neighbors_eq_blue_compl {x : V} :
    (red_neighbors χ) x = insert x ((blue_neighbors χ) x)ᶜ :=
  by
  ext y
  rw [mem_compl, mem_insert, mem_col_neighbors, mem_col_neighbors, not_or]
  simp only [fin.fin_two_eq_zero_iff_ne_one, not_exists]
  constructor
  · rintro ⟨p, q⟩
    exact ⟨p.symm, fun h => q⟩
  rintro ⟨p, q⟩
  exact ⟨Ne.symm p, q _⟩

theorem red_neighbors_inter_eq {x : V} {X : Finset V} (hx : x ∈ X) :
    (red_neighbors χ) x ∩ X = X \ insert x ((blue_neighbors χ) x ∩ X) := by
  rw [red_neighbors_eq_blue_compl, sdiff_eq_inter_compl, inter_comm, ← insert_inter_of_mem hx,
    compl_inter, ← inf_eq_inter, ← sup_eq_union, inf_sup_left, inf_compl_self, sup_bot_eq]

theorem card_red_neighbors_inter {μ : ℝ} (hi : i ∈ redOrDensitySteps μ k l ini) :
    (((red_neighbors χ) (getX hi) ∩ (algorithm μ k l ini i).X).card : ℝ) =
      (1 - blueXRatio μ k l ini i) * (algorithm μ k l ini i).X.card - 1 :=
  by
  rw [red_neighbors_inter_eq, cast_card_sdiff, card_insert_of_not_mem, one_sub_mul,
    Nat.cast_add_one, ← sub_sub, blue_X_ratio_prop]
  · simp [not_mem_col_neighbors]
  · rw [insert_subset]
    exact ⟨book_config.get_central_vertex_mem_X _ _ _, inter_subset_right _ _⟩
  · exact book_config.get_central_vertex_mem_X _ _ _

theorem blue_neighbors_eq_red_compl {x : V} :
    (blue_neighbors χ) x = insert x ((red_neighbors χ) x)ᶜ :=
  by
  ext y
  rw [mem_compl, mem_insert, mem_col_neighbors, mem_col_neighbors, not_or]
  simp only [fin.fin_two_eq_zero_iff_ne_one, not_exists, Classical.not_not]
  constructor
  · rintro ⟨p, q⟩
    exact ⟨p.symm, fun h => q⟩
  rintro ⟨p, q⟩
  exact ⟨_, q (Ne.symm p)⟩

theorem red_neighbors_x_nonempty {μ₁ μ : ℝ} (hμ₁ : μ₁ < 1) (hμu : μ ≤ μ₁) (hk : (1 - μ₁)⁻¹ ≤ k)
    (hl : 1 < l) (hi : i ∈ redOrDensitySteps μ k l ini) :
    ((red_neighbors χ) (getX hi) ∩ (algorithm μ k l ini i).X).Nonempty :=
  by
  set X := (algorithm μ k l ini i).X with ← hx
  have hi' := hi
  rw [red_or_density_steps, mem_filter, mem_range] at hi'
  rw [← card_pos, ← @Nat.cast_pos ℝ, card_red_neighbors_inter, sub_pos]
  suffices 1 < (1 - μ) * X.card
    by
    refine' this.trans_le (mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _))
    rw [sub_le_sub_iff_left]
    exact blue_X_ratio_le_mu hi
  have : (k : ℝ) < X.card := by
    rw [Nat.cast_lt]
    refine' (ramsey_number_lt_of_lt_final_step hi'.1).trans_le' _
    refine' (ramsey_number.mono_two le_rfl _).trans_eq' ramsey_number_two_right.symm
    rw [Nat.add_one_le_ceil_iff, Nat.cast_one]
    exact one_lt_rpow (Nat.one_lt_cast.2 hl) (by norm_num)
  rw [← div_lt_iff' (sub_pos_of_lt (hμ₁.trans_le' hμu)), one_div]
  refine' this.trans_le' (hk.trans' _)
  exact inv_le_inv_of_le (sub_pos_of_lt hμ₁) (sub_le_sub_left hμu _)

theorem five_one_case_a {α : ℝ} (X Y : Finset V) {x : V} (hxX : ((red_neighbors χ) x ∩ X).Nonempty)
    (hxY : ((red_neighbors χ) x ∩ Y).Nonempty) :
    -α * (((red_neighbors χ) x ∩ X).card * ((red_neighbors χ) x ∩ Y).card) / Y.card ≤
        ∑ y in (red_neighbors χ) x ∩ X, pairWeight χ X Y x y →
      (red_density χ) X Y - α ≤
        (red_density χ) ((red_neighbors χ) x ∩ X) ((red_neighbors χ) x ∩ Y) :=
  by
  intro h
  conv_rhs => rw [col_density_eq_sum]
  simp only [pair_weight, ← mul_sum] at h
  rw [inv_mul_eq_div, div_le_div_right, sum_sub_distrib, sum_const, nsmul_eq_mul,
    le_sub_iff_add_le', mul_left_comm, ← add_mul, ← sub_eq_add_neg, ← le_div_iff] at h
  · refine' h.trans_eq _
    congr with i : 2
    rw [inter_left_comm, inter_assoc]
  · positivity
  rw [Nat.cast_pos, card_pos]
  exact hxY.mono (inter_subset_right _ _)

local notation "NB" => blue_neighbors χ

local notation "NR" => red_neighbors χ

theorem five_one_case_b_aux {α : ℝ} (X Y : Finset V) {x : V} (hx : x ∈ X) (hy : Y.Nonempty)
    (h :
      ∑ y in NR x ∩ X, pairWeight χ X Y x y < -α * ((NR x ∩ X).card * (NR x ∩ Y).card) / Y.card) :
    (red_density χ) X Y * ((NB x ∩ X).card * (NR x ∩ Y).card) +
          α * ((NR x ∩ X).card * (NR x ∩ Y).card) +
        weight χ X Y x * Y.card ≤
      ∑ y in NB x ∩ X, (NR y ∩ (NR x ∩ Y)).card :=
  by
  have :
    weight χ X Y x + α * ((NR x ∩ X).card * (NR x ∩ Y).card) / Y.card ≤
      ∑ y in NB x ∩ X, pair_weight χ X Y x y :=
    by
    rw [← le_sub_iff_add_le, sub_eq_add_neg, ← sub_le_iff_le_add', ← neg_div, ← neg_mul]
    refine' h.le.trans_eq' _
    rw [red_neighbors_inter_eq hx, sub_eq_iff_eq_add, insert_eq, sdiff_union_distrib,
      sdiff_singleton_eq_erase, inter_sdiff, (inter_eq_left_iff_subset _ _).2 (erase_subset _ _), ←
      sum_union, sdiff_union_of_subset, weight]
    · rw [subset_erase]
      exact ⟨inter_subset_right _ _, by simp [not_mem_col_neighbors]⟩
    exact disjoint_sdiff_self_left
  simp only [pair_weight, ← mul_sum] at this
  rw [inv_mul_eq_div, le_div_iff, sum_sub_distrib, sum_const, add_mul, div_mul_cancel, nsmul_eq_mul,
    le_sub_iff_add_le', mul_left_comm _ (col_density χ 0 X Y), ← add_assoc, add_right_comm] at this
  · refine' this.trans_eq (sum_congr rfl _)
    intro y hy
    rw [inter_left_comm, inter_assoc]
  positivity
  positivity

theorem five_one_case_b_end (m : ℕ) :
    ∀ᶠ l : ℕ in atTop, ∀ k, l ≤ k → k ^ m ≤ ramseyNumber ![k, ⌈(l : ℝ) ^ (3 / 4 : ℝ)⌉₊] :=
  by
  obtain ⟨c, hc, hf⟩ := five_six_aux_part_one
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_nat_cast_atTop_atTop
  have h34 : (0 : ℝ) < 3 / 4 := by norm_num
  filter_upwards [hf, top_adjuster (t.eventually_ge_at_top 1),
    ((tendsto_rpow_atTop h34).comp t).eventually_ge_atTop (m / c)] with l hl hk₀ hl₁ k hlk
  specialize hk₀ k hlk
  rw [div_le_iff' hc] at hl₁
  rw [← @Nat.cast_le ℝ, Nat.cast_pow, ← rpow_nat_cast]
  refine' (hl k hlk).trans' _
  rw [rpow_def_of_pos, exp_le_exp, mul_comm]
  · exact mul_le_mul_of_nonneg_right hl₁ (log_nonneg hk₀)
  linarith only [hk₀]

theorem five_one_case_b (p₀l : ℝ) (hp₀l : 0 < p₀l) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ : ℝ,
            ∀ n : ℕ,
              ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                ∀ ini : BookConfig χ,
                  p₀l ≤ ini.p →
                    ∀ i : ℕ,
                      ∀ hi : i ∈ redOrDensitySteps μ k l ini,
                        let C := algorithm μ k l ini i
                        ∑ y in (red_neighbors χ) (getX hi) ∩ C.X, pairWeight χ C.X C.y (getX hi) y <
                            -αFunction k (height k ini.p C.p) *
                                (((red_neighbors χ) (getX hi) ∩ C.X).card *
                                  ((red_neighbors χ) (getX hi) ∩ C.y).card) /
                              C.y.card →
                          C.p * blueXRatio μ k l ini i *
                                  (C.X.card * ((red_neighbors χ) (getX hi) ∩ C.y).card) +
                                αFunction k (height k ini.p C.p) * (1 - blueXRatio μ k l ini i) *
                                  (C.X.card * ((red_neighbors χ) (getX hi) ∩ C.y).card) -
                              3 / k ^ 4 * (C.X.card * ((red_neighbors χ) (getX hi) ∩ C.y).card) ≤
                            ∑ y in (blue_neighbors χ) (getX hi) ∩ C.X,
                              ((red_neighbors χ) y ∩ ((red_neighbors χ) (getX hi) ∩ C.y)).card :=
  by
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_nat_cast_atTop_atTop
  filter_upwards [top_adjuster (t.eventually_ge_at_top p₀l⁻¹),
    top_adjuster (t.eventually_gt_at_top (0 : ℝ)), five_eight_weaker' p₀l hp₀l, five_four,
    five_one_case_b_end 4, eventually_ge_at_top (2 ^ 4)] with l hl hk₀ h₅₈ h₅₄ hk₄ hl₄ k hlk μ n χ
    ini hini i hi h
  specialize hl k hlk
  let C := algorithm μ k l ini i
  let x := get_x hi
  let β := blue_X_ratio μ k l ini i
  let α := α_function k (height k ini.p C.p)
  have hx : x ∈ C.X := book_config.get_central_vertex_mem_X _ _ _
  specialize h₅₈ k hlk μ n χ ini hini i x hi hx
  have hi' := hi
  rw [red_or_density_steps, mem_filter, mem_range] at hi'
  have hβ := blue_X_ratio_prop hi
  have hβ' := card_red_neighbors_inter hi
  refine' (five_one_case_b_aux C.X C.Y hx (Y_nonempty hi'.1) h).trans' _
  change
    _ ≤
      C.p * (((blue_neighbors χ) x ∩ C.X).card * ((red_neighbors χ) x ∩ C.Y).card) +
          α * (((red_neighbors χ) x ∩ C.X).card * ((red_neighbors χ) x ∩ C.Y).card) +
        weight χ C.X C.Y x * C.Y.card
  rw [← hβ, hβ', mul_assoc, mul_assoc, sub_one_mul, mul_sub, sub_eq_add_neg (_ * _),
    sub_eq_add_neg _ (_ / _ * _)]
  simp only [← mul_assoc, add_assoc]
  rw [add_le_add_iff_left, add_le_add_iff_left]
  have hp₀ : (1 : ℝ) / k ≤ ini.p := by
    refine' hini.trans' _
    rw [one_div]
    exact inv_le_of_inv_le hp₀l hl
  have : (C.Y.card : ℝ) ≤ k * (2 * ((red_neighbors χ) x ∩ C.Y).card) :=
    by
    rw [mul_left_comm, ← mul_assoc, ← div_le_iff', div_eq_mul_one_div, mul_comm]
    · exact h₅₈
    refine' mul_pos _ (hk₀ k hlk)
    exact two_pos
  have :
    -((2 : ℝ) / k ^ 4) * (C.X.card * ((red_neighbors χ) x ∩ C.Y).card) ≤
      weight χ C.X C.Y x * C.Y.card :=
    by
    refine' (mul_le_mul_of_nonneg_right (h₅₄ k hlk μ n χ ini i hi) (Nat.cast_nonneg _)).trans' _
    rw [neg_mul, neg_div, neg_mul, neg_le_neg_iff]
    refine'
      (mul_le_mul_of_nonneg_left this
            (div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _))).trans_eq
        _
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, mul_left_comm, pow_succ,
      mul_div_mul_left _ _ (hk₀ k hlk).ne', mul_left_comm]
  refine' (add_le_add_left this _).trans' _
  rw [neg_mul, ← neg_add, neg_le_neg_iff, ← mul_assoc, ← add_mul]
  refine' mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [← le_sub_iff_add_le, ← sub_mul, div_sub_div_same, bit1, add_sub_cancel']
  refine'
    (α_le_one col_density_le_one hp₀ (hl₄.trans hlk) (col_density_le_one.trans one_le_two)).trans _
  rw [mul_comm, mul_one_div, one_le_div]
  swap
  · exact pow_pos (hk₀ k hlk) _
  rw [← Nat.cast_pow, Nat.cast_le]
  exact (hk₄ k hlk).trans (ramsey_number_lt_of_lt_final_step hi'.1).le

theorem blueXRatio_le_one {μ : ℝ} : blueXRatio μ k l ini i ≤ 1 :=
  by
  rw [blue_X_ratio]
  split_ifs
  swap
  · exact zero_le_one
  refine' div_le_one_of_le _ (Nat.cast_nonneg _)
  exact Nat.cast_le.2 (card_le_of_subset (inter_subset_right _ _))

theorem five_one_case_b_later (μ₁ : ℝ) (p₀l : ℝ) (hμ₁ : μ₁ < 1) (hp₀l : 0 < p₀l) :
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
                        ∀ hi : i ∈ redOrDensitySteps μ k l ini,
                          let C := algorithm μ k l ini i
                          ∑ y in (red_neighbors χ) (getX hi) ∩ C.X,
                                pairWeight χ C.X C.y (getX hi) y <
                              -αFunction k (height k ini.p C.p) *
                                  (((red_neighbors χ) (getX hi) ∩ C.X).card *
                                    ((red_neighbors χ) (getX hi) ∩ C.y).card) /
                                C.y.card →
                            C.p * blueXRatio μ k l ini i *
                                  (C.X.card * ((red_neighbors χ) (getX hi) ∩ C.y).card) +
                                αFunction k (height k ini.p C.p) * (1 - blueXRatio μ k l ini i) *
                                    (1 - k ^ (-1 / 4 : ℝ)) *
                                  (C.X.card * ((red_neighbors χ) (getX hi) ∩ C.y).card) ≤
                              ∑ y in (blue_neighbors χ) (getX hi) ∩ C.X,
                                ((red_neighbors χ) y ∩ ((red_neighbors χ) (getX hi) ∩ C.y)).card :=
  by
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_nat_cast_atTop_atTop
  have h4 : (0 : ℝ) < -1 / 4 + (-1 / 4 - 1) + 4 := by norm_num
  have := ((tendsto_rpow_atTop h4).comp t).eventually_ge_atTop (3 / (1 - μ₁))
  filter_upwards [five_one_case_b p₀l hp₀l, top_adjuster (t.eventually_gt_at_top 0),
    top_adjuster this] with l hl hk₀ hl' k hlk μ hμu n χ ini hini i hi h
  refine' (hl k hlk μ n χ ini hini i hi h).trans' _
  clear hl
  specialize hk₀ k hlk
  rw [add_sub_assoc, add_le_add_iff_left, ← sub_mul]
  refine' mul_le_mul_of_nonneg_right _ (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  rw [mul_one_sub, sub_le_sub_iff_left, mul_assoc]
  refine' (mul_le_mul_of_nonneg_right five_seven_left _).trans' _
  ·
    exact
      mul_nonneg (sub_nonneg_of_le blue_X_ratio_le_one)
        (rpow_nonneg_of_nonneg (Nat.cast_nonneg _) _)
  rw [← rpow_sub_one hk₀.ne', mul_comm, mul_assoc, ← rpow_add hk₀, ← rpow_nat_cast, Nat.cast_bit0,
    Nat.cast_bit0, Nat.cast_one, div_le_iff (rpow_pos_of_pos hk₀ _), mul_assoc, ← rpow_add hk₀]
  have : 1 - μ ≤ 1 - blue_X_ratio μ k l ini i := sub_le_sub_left (blue_X_ratio_le_mu hi) _
  refine' (mul_le_mul_of_nonneg_right this (rpow_nonneg_of_nonneg (Nat.cast_nonneg _) _)).trans' _
  rw [← div_le_iff' (sub_pos_of_lt (hμ₁.trans_le' hμu))]
  exact
    (hl' k hlk).trans'
      (div_le_div_of_le_left (by norm_num1) (sub_pos_of_lt hμ₁) (sub_le_sub_left hμu _))

theorem α_pos (k h : ℕ) (hk : 0 < k) : 0 < αFunction k h :=
  by
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
  refine' div_pos (mul_pos (rpow_pos_of_pos hk' _) _) hk'
  exact pow_pos (add_pos_of_nonneg_of_pos zero_le_one (rpow_pos_of_pos hk' _)) _

theorem α_nonneg (k h : ℕ) : 0 ≤ αFunction k h :=
  div_nonneg
    (mul_nonneg (rpow_nonneg_of_nonneg (Nat.cast_nonneg _) _)
      (pow_nonneg (add_nonneg zero_le_one (rpow_nonneg_of_nonneg (Nat.cast_nonneg _) _)) _))
    (Nat.cast_nonneg _)

theorem five_one_case_b_condition (μ₁ p₀l : ℝ) (hμ₁ : μ₁ < 1) (hp₀l : 0 < p₀l) :
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
                        ∀ hi : i ∈ redOrDensitySteps μ k l ini,
                          let C := algorithm μ k l ini i
                          ∑ y in (red_neighbors χ) (getX hi) ∩ C.X,
                                pairWeight χ C.X C.y (getX hi) y <
                              -αFunction k (height k ini.p C.p) *
                                  (((red_neighbors χ) (getX hi) ∩ C.X).card *
                                    ((red_neighbors χ) (getX hi) ∩ C.y).card) /
                                C.y.card →
                            ((blue_neighbors χ) (getX hi) ∩ C.X).Nonempty :=
  by
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_nat_cast_atTop_atTop
  filter_upwards [five_one_case_b_later μ₁ p₀l hμ₁ hp₀l,
    top_adjuster (t.eventually_ge_at_top p₀l⁻¹), eventually_gt_at_top 1,
    top_adjuster (t.eventually_gt_at_top (1 : ℝ)), top_adjuster ε_lt_one] with l hl hl' hl₁ hk₁ hε k
    hlk μ hμu n χ ini hini i hi h
  specialize hl k hlk μ hμu n χ ini hini i hi h
  specialize hk₁ k hlk
  refine' nonempty_of_ne_empty _
  intro hXB
  have hβ : blue_X_ratio μ k l ini i = 0 := by
    rw [blue_X_ratio_eq hi, hXB, card_empty, Nat.cast_zero, zero_div]
  rw [hXB, hβ, sum_empty, MulZeroClass.mul_zero, MulZeroClass.zero_mul, zero_add, sub_zero,
    mul_one] at hl
  have hp₀ : (1 : ℝ) / k ≤ ini.p := by
    refine' hini.trans' _
    rw [one_div]
    exact inv_le_of_inv_le hp₀l (hl' k hlk)
  refine' hl.not_lt _
  refine' mul_pos _ _
  swap
  · rw [← Nat.cast_mul, Nat.cast_pos, pos_iff_ne_zero, mul_ne_zero_iff, ← pos_iff_ne_zero, ←
      pos_iff_ne_zero, card_pos, card_pos]
    refine' ⟨X_nonempty _, _⟩
    · rw [red_or_density_steps, mem_filter, mem_range] at hi
      exact hi.1
    exact
      red_neighbors_Y_nonempty' hp₀ (hl₁.trans_le hlk) hi _
        (book_config.get_central_vertex_mem_X _ _ _)
  have hk₀ : (0 : ℝ) < k := hk₁.trans_le' zero_le_one
  refine' mul_pos _ _
  · exact α_pos _ _ (Nat.cast_pos.1 hk₀)
  refine' sub_pos_of_lt _
  exact hε k hlk

theorem five_one (μ₁ p₀l : ℝ) (hμ₁ : μ₁ < 1) (hp₀l : 0 < p₀l) :
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
                        ∀ hi : i ∈ redOrDensitySteps μ k l ini,
                          let C := algorithm μ k l ini i
                          C.p - αFunction k (height k ini.p C.p) ≤
                              (red_density χ) ((red_neighbors χ) (getX hi) ∩ C.X)
                                ((red_neighbors χ) (getX hi) ∩ C.y) ∨
                            0 < blueXRatio μ k l ini i ∧
                              (algorithm μ k l ini i).p +
                                  (1 - k ^ (-1 / 4 : ℝ)) *
                                      ((1 - blueXRatio μ k l ini i) / blueXRatio μ k l ini i) *
                                    αFunction k (height k ini.p C.p) ≤
                                (red_density χ) ((blue_neighbors χ) (getX hi) ∩ C.X)
                                  ((red_neighbors χ) (getX hi) ∩ C.y) :=
  by
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_nat_cast_atTop_atTop
  filter_upwards [top_adjuster (t.eventually_ge_at_top p₀l⁻¹),
    top_adjuster (t.eventually_ge_at_top (1 - μ₁)⁻¹), eventually_gt_at_top 1,
    five_one_case_b_later μ₁ p₀l hμ₁ hp₀l, five_one_case_b_condition μ₁ p₀l hμ₁ hp₀l] with l hkp hkμ
    hl₁ h₁ h₂ k hlk μ hμu n χ ini hini i hi
  let C := algorithm μ k l ini i
  let α := α_function k (height k ini.p C.p)
  let x := get_x hi
  let β := blue_X_ratio μ k l ini i
  let ε : ℝ := k ^ (-1 / 4 : ℝ)
  let Yr := (red_neighbors χ) x ∩ C.Y
  change
    C.p - α ≤ (red_density χ) ((red_neighbors χ) x ∩ C.X) Yr ∨
      0 < β ∧ C.p + (1 - ε) * ((1 - β) / β) * α ≤ (red_density χ) ((blue_neighbors χ) x ∩ C.X) Yr
  have hp₀ : (1 : ℝ) / k ≤ ini.p := by
    refine' hini.trans' _
    rw [one_div]
    exact inv_le_of_inv_le hp₀l (hkp k hlk)
  have hYr : Yr.nonempty :=
    red_neighbors_Y_nonempty' hp₀ (hl₁.trans_le hlk) hi _
      (book_config.get_central_vertex_mem_X _ _ _)
  have hX : C.X.nonempty := by
    refine' X_nonempty _
    rw [red_or_density_steps, mem_filter, mem_range] at hi
    exact hi.1
  cases'
    le_or_lt (-α * (((red_neighbors χ) x ∩ C.X).card * Yr.card) / C.Y.card)
      (∑ y in (red_neighbors χ) x ∩ C.X, pair_weight χ C.X C.Y x y) with
    hα hα
  · exact Or.inl (five_one_case_a _ _ (red_neighbors_X_nonempty hμ₁ hμu (hkμ k hlk) hl₁ hi) hYr hα)
  replace h₁ :
    C.p * β * (C.X.card * Yr.card) + α * (1 - β) * (1 - ε) * (C.X.card * Yr.card) ≤
      ∑ y in (blue_neighbors χ) x ∩ C.X, ((red_neighbors χ) y ∩ Yr).card :=
    h₁ k hlk μ hμu n χ ini hini i hi hα
  replace h₂ : ((blue_neighbors χ) x ∩ C.X).Nonempty := h₂ k hlk μ hμu n χ ini hini i hi hα
  right
  have hβ : 0 < β := by
    change 0 < blue_X_ratio _ _ _ _ _
    rw [blue_X_ratio_eq hi]
    exact div_pos (Nat.cast_pos.2 (card_pos.2 h₂)) (Nat.cast_pos.2 (card_pos.2 hX))
  refine' ⟨hβ, _⟩
  rw [col_density_eq_sum, le_div_iff, ← blue_X_ratio_prop hi, add_mul]
  swap
  · rw [← Nat.cast_mul, ← card_product, Nat.cast_pos, card_pos, nonempty_product]
    exact ⟨h₂, hYr⟩
  refine' h₁.trans' _
  rw [mul_assoc, ← mul_assoc, add_le_add_iff_left, ← mul_assoc]
  refine' mul_le_mul_of_nonneg_right _ (by positivity)
  rw [mul_div_assoc', div_mul_eq_mul_div, div_mul_cancel _ hβ.ne']
  refine' le_of_eq _
  rw [mul_right_comm, mul_rotate]

theorem five_two (μ₁ p₀l : ℝ) (hμ₁ : μ₁ < 1) (hp₀l : 0 < p₀l) :
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
                          0 < blueXRatio μ k l ini i ∧
                            (1 - (k : ℝ) ^ (-1 / 4 : ℝ)) *
                                  ((1 - blueXRatio μ k l ini i) / blueXRatio μ k l ini i) *
                                αFunction k (height k ini.p (algorithm μ k l ini i).p) ≤
                              (algorithm μ k l ini (i + 1)).p - (algorithm μ k l ini i).p :=
  by
  filter_upwards [five_one μ₁ p₀l hμ₁ hp₀l] with l hl k hlk μ hμu n χ ini hini i hi
  have hi' := hi
  simp only [density_steps, mem_image, Subtype.coe_mk, mem_filter, mem_attach, true_and_iff,
    exists_prop, Subtype.exists, exists_and_right, exists_eq_right] at hi'
  obtain ⟨hi'', hhi''⟩ := hi'
  obtain ⟨hβ', h⟩ := (hl k hlk μ hμu n χ ini hini i hi'').resolve_left hhi''.not_le
  refine' ⟨hβ', _⟩
  rw [le_sub_iff_add_le']
  refine' h.trans _
  rw [density_applied hi]
  rfl

theorem blueXRatio_pos (μ₁ p₀l : ℝ) (hμ₁ : μ₁ < 1) (hp₀l : 0 < p₀l) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ,
            μ ≤ μ₁ →
              ∀ n : ℕ,
                ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                  ∀ ini : BookConfig χ,
                    p₀l ≤ ini.p →
                      ∀ i : ℕ, i ∈ densitySteps μ k l ini → 0 < blueXRatio μ k l ini i :=
  by
  filter_upwards [five_two μ₁ p₀l hμ₁ hp₀l] with l hl k hlk μ hμu n χ ini hini i hi
  exact (hl k hlk μ hμu n χ ini hini i hi).1

theorem five_three_left (μ₁ p₀l : ℝ) (hμ₁ : μ₁ < 1) (hp₀l : 0 < p₀l) :
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
  by
  filter_upwards [five_two μ₁ p₀l hμ₁ hp₀l, top_adjuster ε_lt_one] with l hl hε k hlk μ hμu n χ ini
    hini i hi
  rw [← sub_nonneg]
  refine' (hl _ hlk _ hμu _ _ _ hini _ hi).2.trans' _
  refine'
    mul_nonneg
      (mul_nonneg (sub_pos_of_lt (hε k hlk)).le
        (div_nonneg (sub_nonneg_of_le _) blue_X_ratio_nonneg))
      (α_nonneg _ _)
  exact blue_X_ratio_le_one

theorem five_three_right (μ₁ p₀l : ℝ) (hμ₁ : μ₁ < 1) (hp₀l : 0 < p₀l) :
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
                        i ∈ densitySteps μ k l ini → (1 : ℝ) / k ^ 2 ≤ blueXRatio μ k l ini i :=
  by
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_nat_cast_atTop_atTop
  have h54 := tendsto_rpow_atTop (show (0 : ℝ) < 5 / 4 by norm_num)
  have h34 := tendsto_rpow_atTop (show (0 : ℝ) < 3 / 4 by norm_num)
  have h := (tendsto_at_top_add_const_right _ (-2) h34).atTop_mul_atTop h54
  have := tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 4 by norm_num)
  have := eventually_le_of_tendsto_lt (show (0 : ℝ) < 1 - 2⁻¹ by norm_num) this
  filter_upwards [five_two μ₁ p₀l hμ₁ hp₀l, top_adjuster (t.eventually this),
    top_adjuster (t.eventually_gt_at_top 0), top_adjuster ((h.comp t).eventually_ge_atTop 1)] with l
    hl hl' hk₀ hk' k hlk μ hμu n χ ini hini i hi
  specialize hk₀ k hlk
  obtain ⟨hβ, h⟩ := hl k hlk μ hμu n χ ini hini i hi
  have : (algorithm μ k l ini (i + 1)).p - (algorithm μ k l ini i).p ≤ 1 :=
    (sub_le_self _ col_density_nonneg).trans col_density_le_one
  replace h := h.trans this
  rw [mul_right_comm] at h
  have : (1 : ℝ) / 2 ≤ 1 - k ^ (-1 / 4 : ℝ) :=
    by
    rw [le_sub_comm, one_div, neg_div]
    exact hl' k hlk
  have :
    (1 : ℝ) / (2 * k ^ (5 / 4 : ℝ)) ≤
      (1 - k ^ (-1 / 4 : ℝ)) * α_function k (height k ini.p (algorithm μ k l ini i).p) :=
    by
    rw [one_div, mul_inv, ← one_div]
    refine'
      mul_le_mul this _ (inv_nonneg.2 (rpow_nonneg_of_nonneg (Nat.cast_nonneg _) _))
        (this.trans' (by norm_num1))
    rw [← rpow_neg (Nat.cast_nonneg k)]
    refine' five_seven_left.trans_eq' _
    rw [← rpow_sub_one]
    · norm_num
    exact hk₀.ne'
  replace h := (mul_le_mul_of_nonneg_right this _).trans h
  swap
  · refine' div_nonneg (sub_nonneg_of_le _) blue_X_ratio_nonneg
    exact blue_X_ratio_le_one
  rw [mul_comm, mul_one_div, sub_div, div_self hβ.ne', div_le_iff, one_mul, sub_le_iff_le_add] at h
  swap
  · exact mul_pos two_pos (rpow_pos_of_pos hk₀ _)
  rw [one_div]
  refine' inv_le_of_inv_le hβ _
  rw [← one_div]
  refine' h.trans _
  rw [← le_sub_iff_add_le']
  refine' (hk' k hlk).trans_eq _
  dsimp
  rw [← sub_eq_add_neg, sub_mul, sub_left_inj, ← rpow_nat_cast, ← rpow_add']
  · norm_num1
    rfl
  · exact Nat.cast_nonneg _
  norm_num1

end SimpleGraph

