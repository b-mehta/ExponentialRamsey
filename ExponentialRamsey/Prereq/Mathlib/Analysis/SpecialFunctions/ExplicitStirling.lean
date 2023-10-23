/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Data.Nat.Choose.Bounds
import Data.Nat.Choose.Central
import Data.Nat.Choose.Cast
import Analysis.SpecialFunctions.Stirling
import Analysis.SpecialFunctions.Exponential
import Topology.MetricSpace.CauSeqFilter

#align_import prereq.mathlib.analysis.special_functions.explicit_stirling

/-!
# Unconditional bounds on the central binomial coefficient from Stirling approximations
-/


noncomputable section

open scoped Topology Real Nat

open Finset Filter Nat Real

theorem centralBinom_ratio {α : Type _} [Field α] [CharZero α] (n : ℕ) :
    (centralBinom (n + 1) : α) / centralBinom n = 4 * ((n + 1 / 2) / (n + 1)) :=
  by
  rw [mul_div_assoc', mul_add, eq_div_iff, ← cast_add_one, div_mul_eq_mul_div, mul_comm, ← cast_mul,
    succ_mul_central_binom_succ, cast_mul, mul_div_cancel]
  · rw [mul_add_one, ← mul_assoc, cast_add, cast_mul]
    norm_num1
    rfl
  · rw [Nat.cast_ne_zero]
    exact central_binom_ne_zero _
  exact Nat.cast_add_one_ne_zero _

theorem upper_monotone_aux (n : ℕ) :
    ((n : ℝ) + 1 / 2) / (n + 1) ≤ sqrt (n + 1 / 3) / sqrt (n + 1 + 1 / 3) :=
  by
  rw [← Real.sqrt_div]
  refine' Real.le_sqrt_of_sq_le _
  rw [div_pow, div_le_div_iff]
  · ring_nf
    rw [add_le_add_iff_right]
    refine' mul_le_mul_of_nonneg_right _ (by positivity)
    rw [add_le_add_iff_left]
    norm_num1
  all_goals positivity

theorem lower_monotone_aux (n : ℕ) :
    Real.sqrt (n + 1 / 4) / Real.sqrt (n + 1 + 1 / 4) ≤ (n + 1 / 2) / (n + 1) :=
  by
  rw [← Real.sqrt_div, sqrt_le_left, div_pow, div_le_div_iff]
  · ring_nf
    rw [add_le_add_iff_left]
    norm_num1
  all_goals positivity

/-- an explicit function of the central binomial coefficient which we will show is always less than
√π, to get a lower bound on the central binomial coefficient
-/
def centralBinomialLower (n : ℕ) : ℝ :=
  centralBinom n * sqrt (n + 1 / 4) / 4 ^ n

theorem centralBinomialLower_monotone : Monotone centralBinomialLower :=
  by
  refine' monotone_nat_of_le_succ _
  intro n
  rw [centralBinomialLower, centralBinomialLower, pow_succ, ← div_div]
  refine' div_le_div_of_le (by positivity) _
  rw [le_div_iff, mul_assoc, mul_comm, ← div_le_div_iff, centralBinom_ratio, mul_comm,
    mul_div_assoc, Nat.cast_add_one]
  refine' mul_le_mul_of_nonneg_left (lower_monotone_aux n) (by positivity)
  · positivity
  · rw [Nat.cast_pos]
    exact central_binom_pos _
  · positivity

/-- an explicit function of the central binomial coefficient which we will show is always more than
√π, to get an upper bound on the central binomial coefficient
-/
def centralBinomialUpper (n : ℕ) : ℝ :=
  centralBinom n * sqrt (n + 1 / 3) / 4 ^ n

theorem centralBinomialUpper_monotone : Antitone centralBinomialUpper :=
  by
  refine' antitone_nat_of_succ_le _
  intro n
  rw [centralBinomialUpper, centralBinomialUpper, pow_succ, ← div_div]
  refine' div_le_div_of_le (by positivity) _
  rw [div_le_iff, mul_assoc, mul_comm _ (_ * _), ← div_le_div_iff, mul_comm, mul_div_assoc,
    centralBinom_ratio, Nat.cast_add_one]
  refine' mul_le_mul_of_nonneg_left (upper_monotone_aux _) (by positivity)
  · rw [Nat.cast_pos]
    exact central_binom_pos _
  · positivity
  · positivity

theorem centralBinom_limit :
    Tendsto (fun n => (centralBinom n : ℝ) * sqrt n / 4 ^ n) atTop (𝓝 (sqrt π)⁻¹) :=
  by
  have := Real.pi_pos
  have : (sqrt π)⁻¹ = sqrt π / sqrt π ^ 2 := by rw [inv_eq_one_div, sq, ← div_div, div_self];
    positivity
  rw [this]
  have : tendsto (fun n => Stirling.stirlingSeq (2 * n)) at_top (𝓝 (sqrt π)) :=
    by
    refine' tendsto.comp Stirling.tendsto_stirlingSeq_sqrt_pi _
    exact tendsto_id.const_mul_at_top' two_pos
  refine' (this.div (stirling.tendsto_stirling_seq_sqrt_pi.pow 2) (by positivity)).congr' _
  filter_upwards [eventually_gt_at_top (0 : ℕ)] with n hn
  dsimp
  rw [Stirling.stirlingSeq, Stirling.stirlingSeq, central_binom, two_mul n, cast_add_choose, ←
    two_mul, Nat.cast_mul, Nat.cast_two, ← mul_assoc, sqrt_mul' _ (Nat.cast_nonneg _),
    sqrt_mul_self, div_mul_eq_mul_div, div_div, mul_div_assoc, mul_pow, div_pow (n ! : ℝ), mul_pow,
    pow_mul, ← pow_mul (_ / _), mul_comm n, sq_sqrt, mul_div_assoc', ← mul_assoc, mul_right_comm,
    mul_div_mul_right, mul_assoc, mul_comm (_ * _), ← div_div_eq_mul_div, mul_div_mul_left,
    div_sqrt, div_div_eq_mul_div, div_div, sq, sq, mul_comm _ (_ * _), ← bit0_eq_two_mul (2 : ℝ)]
  all_goals positivity

theorem centralBinomialUpper_limit : Tendsto centralBinomialUpper atTop (𝓝 (sqrt π)⁻¹) :=
  by
  have : (sqrt π)⁻¹ = (sqrt π)⁻¹ / sqrt 1 := by rw [Real.sqrt_one, div_one]
  have h : Real.sqrt 1 ≠ 0 := sqrt_ne_zero'.2 zero_lt_one
  rw [this]
  refine' (central_binom_limit.div (tendsto_coe_nat_div_add_atTop (1 / 3 : ℝ)).sqrt h).congr' _
  filter_upwards [eventually_gt_at_top 0] with n hn
  dsimp
  rw [sqrt_div, centralBinomialUpper, div_div, mul_div_assoc', div_div_eq_mul_div, mul_right_comm,
    mul_div_mul_right]
  · positivity
  · positivity

theorem centralBinomialLower_limit : Tendsto centralBinomialLower atTop (𝓝 (sqrt π)⁻¹) :=
  by
  have : (sqrt π)⁻¹ = (sqrt π)⁻¹ / sqrt 1 := by rw [Real.sqrt_one, div_one]
  have h : Real.sqrt 1 ≠ 0 := sqrt_ne_zero'.2 zero_lt_one
  rw [this]
  refine' (central_binom_limit.div (tendsto_coe_nat_div_add_atTop (1 / 4 : ℝ)).sqrt h).congr' _
  filter_upwards [eventually_gt_at_top 0] with n hn
  dsimp
  rw [sqrt_div, centralBinomialLower, div_div, mul_div_assoc', div_div_eq_mul_div, mul_right_comm,
    mul_div_mul_right]
  · positivity
  · positivity

theorem central_binomial_upper_bound (n : ℕ) :
    (n.centralBinom : ℝ) ≤ 4 ^ n / sqrt (π * (n + 1 / 4)) :=
  by
  have := pi_pos
  have := central_binomial_lower_monotone.ge_of_tendsto centralBinomialLower_limit n
  rwa [sqrt_mul, ← div_div, le_div_iff, div_eq_mul_one_div (4 ^ n : ℝ), ← div_le_iff',
    one_div (sqrt π)]
  all_goals positivity

theorem central_binomial_lower_bound (n : ℕ) : 4 ^ n / sqrt (π * (n + 1 / 3)) ≤ n.centralBinom :=
  by
  have := pi_pos
  have := central_binomial_upper_monotone.le_of_tendsto centralBinomialUpper_limit n
  rwa [sqrt_mul, ← div_div, div_le_iff, div_eq_mul_one_div, ← le_div_iff', one_div (sqrt π)]
  all_goals positivity

theorem cexp_eq_tsum {x : ℂ} : Complex.exp x = ∑' i, x ^ i / i ! := by
  rw [Complex.exp_eq_exp_ℂ, exp_eq_tsum_div]

theorem rexp_eq_tsum {x : ℝ} : Real.exp x = ∑' i, x ^ i / i ! := by
  rw [exp_eq_exp_ℝ, exp_eq_tsum_div]

theorem exp_factorial_bound {n : ℕ} : (n : ℝ) ^ n / n ! ≤ exp n :=
  by
  rw [rexp_eq_tsum]
  refine' (sum_le_tsum {n} _ (Real.summable_pow_div_factorial _)).trans' _
  · intro x hx
    positivity
  rw [sum_singleton]

theorem exp_factorial_bound_of_ne_zero {n : ℕ} (hn : n ≠ 0) : (n : ℝ) ^ n / n ! < exp n :=
  by
  rw [rexp_eq_tsum]
  refine' (sum_le_tsum {n, 0} _ (Real.summable_pow_div_factorial _)).trans_lt' _
  · intro x hx
    positivity
  rw [sum_pair hn]
  simp

theorem factorial_bound_exp {n : ℕ} : ((n : ℝ) / Real.exp 1) ^ n ≤ n ! :=
  by
  rw [div_pow, ← rpow_nat_cast (exp 1), exp_one_rpow, div_le_iff, ← div_le_iff']
  · exact exp_factorial_bound
  · positivity
  · positivity

theorem factorial_bound_exp_of_ne_zero {n : ℕ} (hn : n ≠ 0) : ((n : ℝ) / Real.exp 1) ^ n < n ! :=
  by
  rw [div_pow, ← rpow_nat_cast (exp 1), exp_one_rpow, div_lt_iff, ← div_lt_iff']
  · exact exp_factorial_bound_of_ne_zero hn
  · positivity
  · positivity

theorem choose_upper_bound {n t : ℕ} : (n.choose t : ℝ) ≤ (exp 1 * n / t) ^ t :=
  by
  cases Nat.eq_zero_or_pos t
  · simp [h]
  refine' (Nat.choose_le_pow t n).trans _
  refine' (div_le_div_of_le_left _ _ factorial_bound_exp).trans _
  · positivity
  · positivity
  rw [← div_pow, div_div_eq_mul_div, mul_comm]

theorem choose_upper_bound_of_pos {n t : ℕ} (hn : n ≠ 0) (ht : t ≠ 0) :
    (n.choose t : ℝ) < (exp 1 * n / t) ^ t :=
  by
  refine' (Nat.choose_le_pow t n).trans_lt _
  refine' (div_lt_div_of_lt_left _ _ (factorial_bound_exp_of_ne_zero ht)).trans_eq _
  · positivity
  · positivity
  rw [← div_pow, div_div_eq_mul_div, mul_comm]

theorem choose_upper_bound' {n t : ℕ} : (n.choose t : ℝ) ≤ exp t * (n / t) ^ t :=
  choose_upper_bound.trans_eq <| by rw [mul_div_assoc, mul_pow, ← exp_one_rpow t, rpow_nat_cast]

