/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Section11
import Log2Estimates
import LogSmall

/-!
# Numerical calculations and appendix A
-/


open Set Real SimpleGraph

section Interval

theorem add_interval {x y a b c d : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d) :
    x + y ∈ Icc (a + c) (b + d) := by simp only [mem_Icc] at hx hy ⊢ <;> constructor <;> linarith

theorem sub_interval {x y a b c d : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d) :
    x - y ∈ Icc (a - d) (b - c) := by simp only [mem_Icc] at hx hy ⊢ <;> constructor <;> linarith

theorem hMul_interval {x y a b c d : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d) (ha : 0 < a)
    (hc : 0 < c) : x * y ∈ Icc (a * c) (b * d) := by
  simp only [mem_Icc] at hx hy ⊢ <;> constructor <;> nlinarith

theorem hMul_interval_of_neg_pos {x y a b c d : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d)
    (ha : b < 0) (hc : 0 < c) : x * y ∈ Icc (a * d) (b * c) := by
  simp only [mem_Icc] at hx hy ⊢ <;> constructor <;> nlinarith

theorem hMul_interval_of_pos_neg {x y a b c d : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d)
    (ha : 0 < a) (hc : d < 0) : x * y ∈ Icc (b * c) (a * d) := by
  simp only [mem_Icc] at hx hy ⊢ <;> constructor <;> nlinarith

theorem hMul_interval_of_neg {x y a b c d : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d) (hb : b < 0)
    (hc : d < 0) : x * y ∈ Icc (b * d) (a * c) := by
  simp only [mem_Icc] at hx hy ⊢ <;> constructor <;> nlinarith

theorem const_interval {x : ℝ} : x ∈ Icc x x := by simp

theorem neg_interval {x a b : ℝ} (hx : x ∈ Icc a b) : -x ∈ Icc (-b) (-a) := by
  rwa [← preimage_neg_Icc, neg_mem_neg]

theorem interval_end {x a b c d : ℝ} (hx : x ∈ Icc a b) (hca : c ≤ a) (hbd : b ≤ d) : x ∈ Icc c d :=
  Icc_subset_Icc hca hbd hx

end Interval

section SimpleValues

theorem one_div_log_two_interval :
    1 / log 2 ∈ Icc (1.442695040888963407 : ℝ) 1.442695040888963408 :=
  by
  rw [mem_Icc, le_one_div _ (log_pos one_lt_two), one_div_le (log_pos one_lt_two)]
  · exact ⟨log_two_lt_d20.le.trans (by norm_num1), log_two_gt_d20.le.trans' (by norm_num1)⟩
  · norm_num1
  · norm_num1

theorem log_three_interval : log 3 ∈ Icc (1.0986122886681096 : ℝ) 1.0986122886681097 :=
  ⟨log_three_gt_d20.le, log_three_lt_d20.le⟩

-- 1.5849625007211561814537389439478165087598144076924810604557526545...
theorem logb_two_three_interval : logb 2 3 ∈ Icc (1.58496250072115 : ℝ) 1.58496250072116 :=
  by
  rw [logb, div_eq_mul_one_div]
  refine' interval_end (hMul_interval log_three_interval one_div_log_two_interval _ _) _ _ <;>
    norm_num1

theorem log_five_interval : log 5 ∈ Icc (1.609437912434100374 : ℝ) 1.609437912434100375 :=
  ⟨log_five_gt_d20.le, log_five_lt_d20.le⟩

-- 2.3219280948873623478703194294893901758648313930245806120547563958...
theorem logb_two_five_interval : logb 2 5 ∈ Icc (2.32192809488736234 : ℝ) 2.32192809488736235 :=
  by
  rw [logb, div_eq_mul_one_div]
  refine' interval_end (hMul_interval log_five_interval one_div_log_two_interval _ _) _ _ <;>
    norm_num1

end SimpleValues

section Generic

theorem log_of_neg {x : ℝ} : log (-x) = log x := by rw [← log_abs, abs_neg, log_abs]

theorem logb_of_neg {b x : ℝ} : logb b (-x) = logb b x := by rw [logb, log_of_neg, logb]

theorem hMul_binEnt_inv {x : ℝ} : x * binEnt 2 (1 / x) = -binEnt 2 x :=
  by
  rcases eq_or_ne x 0 with (rfl | hx₀)
  · simp
  rcases eq_or_ne x 1 with (rfl | hx₁)
  · simp
  have : 1 - x⁻¹ = x⁻¹ * -(1 - x) := by rw [neg_sub, mul_sub_one, inv_mul_cancel hx₀]
  rw [binEnt, binEnt, one_div, this, mul_neg, logb_of_neg, logb_mul, logb_inv, neg_mul_neg, neg_mul,
    sub_neg_eq_add, mul_assoc, ← mul_add, mul_inv_cancel_left₀ hx₀]
  · ring_nf
  · rwa [Ne.def, inv_eq_zero]
  · rwa [sub_ne_zero, ne_comm]

theorem binEnt_one_half : binEnt 2 (1 / 2) = 1 :=
  by
  rw [binEnt]
  norm_num1
  rw [one_div, logb_inv, logb_base two_pos one_lt_two.ne']
  norm_num1

-- lemma logb_two_three_lower : 1054 / 665 < logb 2 3 :=
-- begin
--   rw [div_lt_iff, mul_comm],
--   swap, { norm_num1 },
--   have : (665 : ℝ) = (665 : ℕ) := by norm_num1,
--   rw [this, ←_root_.logb_pow, lt_logb_iff_rpow_lt],
--   { norm_num1 },
--   { norm_num1 },
--   exact pow_pos (by norm_num1) _,
-- end
-- lemma logb_two_three_upper : logb 2 3 < 485 / 306 :=
-- begin
--   rw [lt_div_iff, mul_comm],
--   swap, { norm_num1 },
--   have : (306 : ℝ) = (306 : ℕ) := by norm_num1,
--   rw [this, ←_root_.logb_pow, logb_lt_iff_lt_rpow],
--   { norm_num1 },
--   { norm_num1 },
--   exact pow_pos (by norm_num1) _,
-- end
theorem binEnt_one_third : binEnt 2 (1 / 3) = logb 2 3 - 2 / 3 :=
  by
  rw [binEnt]
  norm_num1
  rw [one_div, logb_inv, logb_div, logb_base two_pos one_lt_two.ne']
  · ring_nf
  · norm_num1
  · norm_num1

theorem binEnt_one_third_lower : 0.91 ≤ binEnt 2 (1 / 3) :=
  by
  rw [binEnt_one_third, le_sub_iff_add_le]
  norm_num1
  rw [div_le_iff, mul_comm]
  swap; · norm_num1
  have : (300 : ℝ) = (300 : ℕ) := by norm_num1
  rw [this, ← _root_.logb_pow, le_logb_iff_rpow_le]
  · norm_num1
  · norm_num1
  exact pow_pos (by norm_num1) _

theorem binEnt_one_third_upper : binEnt 2 (1 / 3) ≤ 0.92 :=
  by
  rw [binEnt_one_third, sub_le_iff_le_add]
  norm_num1
  rw [le_div_iff, mul_comm]
  swap; · norm_num1
  have : (75 : ℝ) = (75 : ℕ) := by norm_num1
  rw [this, ← _root_.logb_pow, logb_le_iff_le_rpow]
  · norm_num1
  · norm_num1
  exact pow_pos (by norm_num1) _

theorem log_le_div_exp_of_pos {y : ℝ} (hy : 0 ≤ y) : log y ≤ y / exp 1 :=
  by
  rcases eq_or_lt_of_le hy with (rfl | hy')
  · simp
  have := log_le_sub_one_of_pos (div_pos hy' (exp_pos 1))
  rwa [log_div hy'.ne' (exp_pos _).ne', log_exp, sub_le_sub_iff_right] at this 

theorem neg_log_le_rpow {x : ℝ} (hx : 0 < x) : -log x ≤ x ^ (-1 / exp 1) :=
  by
  have : 0 ≤ x ^ (-1 / exp 1) := by refine' (rpow_pos_of_pos hx _).le
  have := log_le_div_exp_of_pos this
  rwa [log_rpow hx, div_mul_eq_mul_div, neg_one_mul, div_le_iff (exp_pos _),
    div_mul_cancel _ (exp_pos _).ne'] at this 

open Filter

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:38: in filter_upwards #[[], ["with", ident x], ["using", expr abs_nonneg _]]: ./././Mathport/Syntax/Translate/Basic.lean:354:22: unsupported: parse error @ arg 0: next failed, no more args -/
theorem log_hMul_continuous : Continuous fun x => x * log x :=
  by
  rw [continuous_iff_continuousAt]
  intro x
  rcases ne_or_eq x 0 with (hx | rfl)
  · exact continuous_at_id.mul (continuous_at_log hx)
  rw [ContinuousAt, MulZeroClass.zero_mul, tendsto_zero_iff_abs_tendsto_zero]
  have h1e : 0 < 1 - 1 / exp 1 := by
    refine' sub_pos_of_lt _
    rw [div_lt_iff (exp_pos _), one_mul]
    exact exp_one_gt_d9.trans_le' (by norm_num1)
  have : ∀ x : ℝ, 0 < x → x < 1 → |x * log x| ≤ x ^ (1 - 1 / exp 1) :=
    by
    intro x hx₀ hx₁
    rw [abs_mul, abs_of_pos hx₀, abs_of_neg (log_neg hx₀ hx₁), sub_eq_add_neg, rpow_add hx₀,
      rpow_one, ← neg_div]
    exact mul_le_mul_of_nonneg_left (neg_log_le_rpow hx₀) hx₀.le
  have : ∀ x : ℝ, 0 ≤ x → x < 1 → |x * log x| ≤ x ^ (1 - 1 / exp 1) :=
    by
    intro x hx
    rcases lt_or_eq_of_le hx with (hx' | rfl)
    · exact this _ hx'
    intro
    rw [MulZeroClass.zero_mul, abs_zero, zero_rpow h1e.ne']
  have : ∀ᶠ x : ℝ in nhds 0, |x * log x| ≤ |x| ^ (1 - 1 / exp 1) :=
    by
    -- might be useful
    filter_upwards [eventually_abs_sub_lt 0 (zero_lt_one' ℝ)] with x hx
    rw [sub_zero] at hx 
    refine' (this |x| (abs_nonneg _) hx).trans' _
    rw [log_abs, abs_mul, abs_mul, abs_abs]
  refine' squeeze_zero' _ this _
  ·
    trace
      "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:38: in filter_upwards #[[], [\"with\", ident x], [\"using\", expr abs_nonneg _]]: ./././Mathport/Syntax/Translate/Basic.lean:354:22: unsupported: parse error @ arg 0: next failed, no more args"
  suffices tendsto (fun x : ℝ => |x| ^ (1 - 1 / exp 1)) (nhds 0) (nhds (|0| ^ (1 - 1 / exp 1)))
    by
    convert this using 2
    rw [abs_zero, zero_rpow h1e.ne']
  exact (continuous_abs.tendsto _).rpow_const (Or.inr h1e.le)

theorem continuous_logb {b : ℝ} : ContinuousOn (logb b) ({0}ᶜ) :=
  continuousOn_log.div_const _

theorem ContinuousOn.logb {α : Type _} [TopologicalSpace α] {b : ℝ} {f : α → ℝ} {s : Set α}
    (hf : ContinuousOn f s) (hf' : ∀ x ∈ s, f x ≠ 0) : ContinuousOn (fun x => logb b (f x)) s :=
  ContinuousOn.comp continuous_logb hf (by simpa using hf')

theorem binEnt_continuous {b : ℝ} : Continuous fun x => binEnt b x :=
  by
  simp only [binEnt_eq]
  exact
    (log_mul_continuous.neg.add
          (log_mul_continuous.comp (continuous_const.sub continuous_id')).neg).div_const
      _

theorem logb_hMul_continuous {b : ℝ} : Continuous fun x => x * logb b x :=
  by
  simp only [logb, mul_div_assoc']
  refine' log_mul_continuous.div_const _

theorem self_lt_binEnt {x : ℝ} (hx : 0 < x) (hx' : x ≤ 1 / 2) : x < binEnt 2 x :=
  by
  cases le_or_lt (1 / 3) x
  · refine' hx'.trans_lt _
    refine'
      ((strict_mono_on_bin_ent_zero_half one_lt_two).MonotoneOn ⟨_, _⟩ ⟨hx.le, hx'⟩ h).trans_lt' _
    · norm_num1
    · norm_num1
    refine' bin_ent_one_third_lower.trans_lt' _
    norm_num1
  rw [← sub_pos]
  let f : ℝ → ℝ := fun x => binEnt 2 x - x
  have hf0 : f 0 = 0 := by simp [f]
  have h₁ : ∀ x ∈ Ioo (0 : ℝ) (1 / 3), HasDerivAt f (logb 2 (1 - x) - logb 2 x - 1) x :=
    by
    intro x hx
    refine' (bin_ent_deriv 2 x hx.1.ne' _).sub (hasDerivAt_id' x)
    linarith only [hx.2]
  have h₂ : ∀ x : ℝ, x ∈ Ioo (0 : ℝ) (1 / 3) → 0 < logb 2 (1 - x) - logb 2 x - 1 :=
    by
    rintro y ⟨hy₀, hy₁⟩
    rw [sub_pos, ← logb_div _ hy₀.ne', lt_logb_iff_rpow_lt one_lt_two, rpow_one, lt_div_iff hy₀]
    · linarith only [hy₁]
    · refine' div_pos (by linarith only [hy₁]) hy₀
    linarith only [hy₁]
  have : StrictMonoOn f (Icc (0 : ℝ) (1 / 3)) :=
    by
    refine' Convex.strictMonoOn_of_deriv_pos (convex_Icc _ _) _ _
    · exact (bin_ent_continuous.sub continuous_id').ContinuousOn
    rw [interior_Icc]
    intro x hx
    rw [HasDerivAt.deriv (h₁ x hx)]
    exact h₂ x hx
  specialize this ⟨le_rfl, by norm_num1⟩ ⟨hx.le, h.le⟩ hx
  rwa [hf0] at this 

theorem self_le_binEnt {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1 / 2) : x ≤ binEnt 2 x :=
  by
  rcases lt_or_eq_of_le hx with (hx₀ | rfl)
  · exact (self_lt_binEnt hx₀ hx').le
  simp

theorem continuous_on_hMul_binEnt_inv : Continuous fun x => x * binEnt 2 (1 / x) :=
  by
  simp only [hMul_binEnt_inv]
  exact bin_ent_continuous.neg

end Generic

section

open Filter

theorem f_deriv_aux {x : ℝ} (hx : x ≠ 2) :
    HasDerivAt (fun x : ℝ => 1 / (2 - x)) (1 / (2 - x) ^ 2) x := by
  simpa using ((hasDerivAt_id' x).const_sub 2).inv (sub_ne_zero_of_ne hx.symm)

theorem f_deriv_aux2 {x : ℝ} (hx₁ : x ≠ 1) :
    HasDerivAt (fun x : ℝ => x * binEnt 2 x) (2 * binEnt 2 x + logb 2 (1 - x)) x :=
  by
  rcases ne_or_eq x 0 with (hx₀ | rfl)
  · have : HasDerivAt (fun x : ℝ => x * binEnt 2 x) _ x :=
      HasDerivAt.mul (hasDerivAt_id' _) (bin_ent_deriv _ _ hx₀ hx₁)
    convert this using 1
    rw [binEnt]
    ring
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  simp only [zero_add, MulZeroClass.zero_mul, sub_zero, binEnt_zero, logb_one,
    MulZeroClass.mul_zero, smul_zero]
  rw [Asymptotics.isLittleO_iff_tendsto]
  swap
  · rintro x rfl
    simp
  have : ∀ x, x * binEnt 2 x / x = binEnt 2 x :=
    by
    intro x
    rcases eq_or_ne x 0 with (rfl | hx)
    · simp
    rw [mul_div_cancel_left _ hx]
  simp only [this]
  convert (@binEnt_continuous 2).ContinuousAt using 1
  simp

-- nicely defined when 1 < x
theorem f_deriv_aux3 {x : ℝ} (hx₀ : x ≠ 0) (hx₁ : x ≠ 1) :
    HasDerivAt (fun x : ℝ => x * binEnt 2 (1 / x)) (logb 2 x - logb 2 (x - 1)) x :=
  by
  simp only [hMul_binEnt_inv]
  convert (bin_ent_deriv _ _ hx₀ hx₁).neg using 1
  rw [neg_sub, ← neg_sub x, logb_of_neg]

theorem important_rewrite {x : ℝ} (hx : x ≠ 2) : 1 - 1 / (2 - x) = (1 - x) / (2 - x) := by
  rw [one_sub_div (sub_ne_zero_of_ne hx.symm)]; ring_nf

theorem important_rewrite' {x : ℝ} : logb 2 (1 - 1 / (2 - x)) = logb 2 ((1 - x) / (2 - x)) :=
  by
  rcases eq_or_ne x 2 with (rfl | hx₂)
  · norm_num
  rw [important_rewrite hx₂]

theorem important_rewrite2 {x : ℝ} : logb 2 ((1 - x) / (2 - x)) = logb 2 (1 - x) - logb 2 (2 - x) :=
  by
  rcases eq_or_ne x 1 with (rfl | hx₁)
  · norm_num
  rcases eq_or_ne x 2 with (rfl | hx₂)
  · norm_num
  rw [logb_div (sub_ne_zero_of_ne hx₁.symm) (sub_ne_zero_of_ne hx₂.symm)]

theorem f1_deriv_helper {x : ℝ} (hx₁ : x ≠ 1) (hx₂ : x ≠ 2) :
    HasDerivAt (fun x => (2 - x) * binEnt 2 (1 / (2 - x))) (logb 2 ((1 - x) / (2 - x))) x :=
  by
  have :
    HasDerivAt (fun x => (2 - x) * binEnt 2 (1 / (2 - x)))
      ((logb 2 (2 - x) - logb 2 (2 - x - 1)) * -1) x :=
    by
    refine' (f_deriv_aux3 _ _).comp _ (HasDerivAt.const_sub 2 (hasDerivAt_id' x))
    · exact sub_ne_zero_of_ne hx₂.symm
    contrapose! hx₁
    linarith only [hx₁]
  convert this using 1
  rw [mul_neg_one, neg_sub, important_rewrite2]
  ring_nf

theorem f1_deriv {x y : ℝ} (hx₁ : x ≠ 1) (hx₂ : x ≠ 2) :
    HasDerivAt (fun x' => f1 x' y) (1 + logb 2 ((1 - x) / (2 - x))) x :=
  ((hasDerivAt_id' _).AddConst _).add (f1_deriv_helper hx₁ hx₂)

theorem continuous_on_f1 {y : ℝ} : Continuous fun x => f1 x y :=
  by
  refine' (continuous_id'.add continuous_const).add _
  exact continuous_on_mul_bin_ent_inv.comp (continuous_const.sub continuous_id')

theorem strictAntiOn_f1 {y : ℝ} : StrictAntiOn (fun x => f1 x y) (Icc (0 : ℝ) 1) :=
  by
  refine' Convex.strictAntiOn_of_deriv_neg (convex_Icc _ _) _ _
  · exact continuous_on_f1.continuous_on
  rw [interior_Icc]
  intro x hx
  rw [(f1_deriv hx.2.Ne (by linarith only [hx.2])).deriv]
  have : 0 < 2 - x := by linarith only [hx.2]
  rw [← lt_neg_iff_add_neg', logb_lt_iff_lt_rpow one_lt_two (div_pos (sub_pos_of_lt hx.2) this),
    div_lt_iff this, rpow_neg_one, ← one_div]
  linarith [hx.1]

theorem eqOn_f2 {y : ℝ} :
    EqOn (fun x => f2 x y) (fun x => f1 x y - 1 / (log 2 * 40) * (1 - 1 / (2 - x))) ({2}ᶜ) :=
  by
  rintro x hx
  dsimp
  rw [f2, f1, important_rewrite hx]

theorem continuousOn_f2 {y : ℝ} : ContinuousOn (fun x => f2 x y) ({2}ᶜ) :=
  by
  refine' (continuous_on_f1.continuous_on.sub (continuous_on_const.mul _)).congr eqOn_f2
  refine' continuous_on_const.sub _
  simp only [one_div]
  refine' (continuous_const.sub continuous_id').ContinuousOn.inv₀ _
  intro x
  rw [sub_ne_zero]
  exact Ne.symm

theorem f2_hasDerivAt {x y : ℝ} (hx₁ : x ≠ 1) (hx₂ : x ≠ 2) :
    HasDerivAt (fun x => f2 x y)
      (1 + logb 2 ((1 - x) / (2 - x)) + 1 / (log 2 * 40) * (1 / (2 - x) ^ 2)) x :=
  by
  refine' HasDerivAt.congr_of_eventuallyEq _ (eq_on.eventually_eq_of_mem eqOn_f2 _)
  swap
  · simp only [compl_singleton_mem_nhds_iff]
    exact hx₂
  refine' HasDerivAt.add (f1_deriv hx₁ hx₂) _
  simp only [← mul_neg, neg_sub]
  refine' HasDerivAt.const_mul _ _
  refine' HasDerivAt.sub_const _ _
  exact f_deriv_aux hx₂

theorem strictAntiOn_f2 {y : ℝ} : StrictAntiOn (fun x => f2 x y) (Icc (1 / 2 : ℝ) 1) :=
  by
  refine' Convex.strictAntiOn_of_deriv_neg (convex_Icc _ _) (continuous_on_f2.mono _) _
  · norm_num
  rw [interior_Icc]
  rintro x ⟨hx₁, hx₂⟩
  have h2x : x < 2 := by linarith only [hx₂]
  rw [(f2_hasDerivAt hx₂.ne h2x.ne).deriv]
  have : 0 < log 2 := log_pos one_lt_two
  have h₁ : logb 2 ((1 - x) / (2 - x)) ≤ logb 2 (1 / 3) :=
    by
    refine' _root_.logb_le_logb_of_le one_le_two (div_pos (sub_pos_of_lt hx₂) (sub_pos_of_lt h2x)) _
    rw [div_le_iff (sub_pos_of_lt h2x)]
    linarith only [hx₁]
  rw [one_div, logb_inv] at h₁ 
  replace h₁ : logb 2 ((1 - x) / (2 - x)) < -1.5
  · refine' h₁.trans_lt _
    rw [neg_lt_neg_iff]
    refine' logb_two_three_interval.1.trans_lt' _
    norm_num1
  have h₂ : 1 / (log 2 * 40) * (1 / (2 - x) ^ 2) ≤ 1 / (log 2 * 40) :=
    by
    refine' mul_le_of_le_one_right _ _
    · positivity
    refine' div_le_one_of_le _ (sq_nonneg _)
    rw [one_le_sq_iff] <;> linarith only [hx₂]
  replace h₂ : 1 / (log 2 * 40) * (1 / (2 - x) ^ 2) ≤ 5e-2
  · refine' h₂.trans _
    rw [mul_comm, ← div_div, div_le_div_iff this, mul_comm, mul_one_div, one_mul]
    · exact log_two_gt_d9.le.trans' (by norm_num1)
    norm_num1
  linarith only [h₁, h₂]

end

section Values

open Real

/-- the first x value to estimate log2 for -/
noncomputable def xValue : ℝ :=
  (0.4339 + 2727 / 8000) / 0.4339

theorem xValue_eq : xValue = 30991 / 17356 := by norm_num [xValue]

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 398549171/250000000], [expr 3985491711/2500000000]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 1270731533/1000000000], [expr 254146307/200000000]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 403689657/250000000], [expr 20184483/12500000]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 130372271/100000000], [expr 3259307/2500000]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 16996929/10000000], [expr 4249233/2500000]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 144447797/100000000], [expr 2888957/2000000]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 10432583/10000000], [expr 10432591/10000000]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 11845881/10000000], [expr 1480741/1250000]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 14032489/10000000], [expr 1403261/1000000]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 1969107/1000000], [expr 984571/500000]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 1938691/1000000], [expr 1938761/1000000]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 1879261/1000000], [expr 939699/500000]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 176581/100000], [expr 176607/100000]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 4872/3125], [expr 155951/100000]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 12153/10000], [expr 12161/10000]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 14769/10000], [expr 14789/10000]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 5453/5000], [expr 1367/1250]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 5947/5000], [expr 299/250]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 7073/5000], [expr 2861/2000]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 2001/2000], [expr 1279/1250]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 1001/1000], [expr 1047/1000]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 501/500], [expr 1097/1000]] -/
theorem logb_xValue : 0.8364148 < logb 2 xValue ∧ logb 2 xValue < 0.8364149 :=
  by
  rw [xValue_eq]
  refine' log_base2_start (by norm_num1) le_rfl _
  refine' log_base2_square _
  refine' log_base2_half _
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 398549171/250000000], [expr 3985491711/2500000000]]"
  refine' log_base2_square _
  refine' log_base2_half _
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 1270731533/1000000000], [expr 254146307/200000000]]"
  refine' log_base2_square _
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 403689657/250000000], [expr 20184483/12500000]]"
  refine' log_base2_square _
  refine' log_base2_half _
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 130372271/100000000], [expr 3259307/2500000]]"
  refine' log_base2_square _
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 16996929/10000000], [expr 4249233/2500000]]"
  refine' log_base2_square _
  refine' log_base2_half _
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 144447797/100000000], [expr 2888957/2000000]]"
  refine' log_base2_square _
  refine' log_base2_half _
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 10432583/10000000], [expr 10432591/10000000]]"
  norm_num1
  refine' log_base2_square _
  refine' log_base2_square _
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 11845881/10000000], [expr 1480741/1250000]]"
  refine' log_base2_square _
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 14032489/10000000], [expr 1403261/1000000]]"
  refine' log_base2_square _
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 1969107/1000000], [expr 984571/500000]]"
  refine' log_base2_square _
  refine' log_base2_half _
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 1938691/1000000], [expr 1938761/1000000]]"
  refine' log_base2_square _
  refine' log_base2_half _
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 1879261/1000000], [expr 939699/500000]]"
  refine' log_base2_square _
  refine' log_base2_half _
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 176581/100000], [expr 176607/100000]]"
  norm_num1
  refine' log_base2_square _
  refine' log_base2_half _
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 4872/3125], [expr 155951/100000]]"
  refine' log_base2_square _
  refine' log_base2_half _
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 12153/10000], [expr 12161/10000]]"
  refine' log_base2_square _
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 14769/10000], [expr 14789/10000]]"
  refine' log_base2_square _
  refine' log_base2_half _
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 5453/5000], [expr 1367/1250]]"
  refine' log_base2_square _
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 5947/5000], [expr 299/250]]"
  refine' log_base2_square _
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 7073/5000], [expr 2861/2000]]"
  refine' log_base2_square _
  refine' log_base2_half _
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 2001/2000], [expr 1279/1250]]"
  refine' log_base2_square _
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 1001/1000], [expr 1047/1000]]"
  refine' log_base2_square _
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 501/500], [expr 1097/1000]]"
  refine' log_base2_square _
  exact log_base2_end (by norm_num1) (by norm_num1) (by norm_num1) (by norm_num1)

theorem logb_two_xValue_interval : logb 2 xValue ∈ Icc (0.8364148 : ℝ) 0.8364149 :=
  ⟨logb_xValue.1.le, logb_xValue.2.le⟩

/-- the second x value to estimate log2 for -/
noncomputable def xValue2 : ℝ :=
  1 / (2 - 0.817)

theorem xValue2_eq : xValue2 = 1000 / 1183 := by norm_num [xValue2]

/-- the third x value to estimate log2 for -/
noncomputable def xValue3 : ℝ :=
  1 - 1 / (2 - 0.817)

theorem xValue3_eq : xValue3 = 183 / 1183 := by norm_num [xValue3]

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 1429093/1000000], [expr 714547/500000]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 1021153/1000000], [expr 204231/200000]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 1042753/1000000], [expr 521379/500000]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 1087333/1000000], [expr 217469/200000]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 1182293/1000000], [expr 14779/12500]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 174727/125000], [expr 139789/100000]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 48847/25000], [expr 19541/10000]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 95441/50000], [expr 95463/50000]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 182179/100000], [expr 22783/12500]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 33189/20000], [expr 166101/100000]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 17211/12500], [expr 34487/25000]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 18957/10000], [expr 190297/100000]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 1123/625], [expr 18107/10000]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 807/500], [expr 41/25]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 13/10], [expr 27/20]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 3/2], [expr 19/10]] -/
theorem logb_approx_second : -0.24246 < logb 2 xValue2 ∧ logb 2 xValue2 < -0.242435 :=
  by
  rw [xValue2_eq]
  refine' log_base2_start (by norm_num1) le_rfl _
  refine' log_base2_scale 1 _
  rw [Int.cast_one]
  norm_num1
  refine' log_base2_square _
  refine' log_base2_half _
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 1429093/1000000], [expr 714547/500000]]"
  refine' log_base2_square _
  refine' log_base2_half _
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 1021153/1000000], [expr 204231/200000]]"
  refine' log_base2_square _
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 1042753/1000000], [expr 521379/500000]]"
  refine' log_base2_square _
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 1087333/1000000], [expr 217469/200000]]"
  refine' log_base2_square _
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 1182293/1000000], [expr 14779/12500]]"
  refine' log_base2_square _
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 174727/125000], [expr 139789/100000]]"
  refine' log_base2_square _
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 48847/25000], [expr 19541/10000]]"
  refine' log_base2_square _
  refine' log_base2_half _
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 95441/50000], [expr 95463/50000]]"
  refine' log_base2_square _
  refine' log_base2_half _
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 182179/100000], [expr 22783/12500]]"
  refine' log_base2_square _
  refine' log_base2_half _
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 33189/20000], [expr 166101/100000]]"
  refine' log_base2_square _
  refine' log_base2_half _
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 17211/12500], [expr 34487/25000]]"
  refine' log_base2_square _
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 18957/10000], [expr 190297/100000]]"
  refine' log_base2_square _
  refine' log_base2_half _
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 1123/625], [expr 18107/10000]]"
  refine' log_base2_square _
  refine' log_base2_half _
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 807/500], [expr 41/25]]"
  refine' log_base2_square _
  refine' log_base2_half _
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 13/10], [expr 27/20]]"
  refine' log_base2_square _
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 3/2], [expr 19/10]]"
  refine' log_base2_square _
  refine' log_base2_half _
  norm_num1
  exact log_base2_end (by norm_num1) (by norm_num1) (by norm_num1) (by norm_num1)

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 5863613513/5000000000], [expr 11727227027/10000000000]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 1375278537/1000000000], [expr 687639269/500000000]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 945695527/500000000], [expr 945695529/500000000]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 35773601/20000000], [expr 178868007/100000000]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 9998051/6250000], [expr 7998441/5000000]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 12795011/10000000], [expr 3198753/2500000]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 1637123/1000000], [expr 409281/250000]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 268017/200000], [expr 167511/125000]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 1795827/1000000], [expr 448959/250000]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 1612497/1000000], [expr 806257/500000]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 130007/100000], [expr 130011/100000]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 16901/10000], [expr 16903/10000]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 7141/5000], [expr 7143/5000]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 509/500], [expr 1021/1000]] -/
---2.692534520055745970309653458812168292098504470773201890789775983...
theorem logb_approx_third : -2.69257 < logb 2 xValue3 ∧ logb 2 xValue3 < -2.69251 :=
  by
  rw [xValue3_eq]
  refine' log_base2_start (by norm_num1) le_rfl _
  refine' log_base2_scale 3 _
  rw [Int.cast_bit1, Int.cast_one]
  refine' log_base2_square _
  refine' log_base2_square _
  refine' log_base2_half _;
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 5863613513/5000000000], [expr 11727227027/10000000000]]"
  refine' log_base2_square _;
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 1375278537/1000000000], [expr 687639269/500000000]]"
  refine' log_base2_square _;
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 945695527/500000000], [expr 945695529/500000000]]"
  refine' log_base2_square _
  refine' log_base2_half _;
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 35773601/20000000], [expr 178868007/100000000]]"
  refine' log_base2_square _
  refine' log_base2_half _;
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 9998051/6250000], [expr 7998441/5000000]]"
  refine' log_base2_square _
  refine' log_base2_half _;
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 12795011/10000000], [expr 3198753/2500000]]"
  refine' log_base2_square _;
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 1637123/1000000], [expr 409281/250000]]"
  refine' log_base2_square _
  refine' log_base2_half _;
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 268017/200000], [expr 167511/125000]]"
  refine' log_base2_square _;
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 1795827/1000000], [expr 448959/250000]]"
  refine' log_base2_square _
  refine' log_base2_half _;
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 1612497/1000000], [expr 806257/500000]]"
  refine' log_base2_square _
  refine' log_base2_half _;
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 130007/100000], [expr 130011/100000]]"
  refine' log_base2_square _;
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 16901/10000], [expr 16903/10000]]"
  refine' log_base2_square _
  refine' log_base2_half _;
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 7141/5000], [expr 7143/5000]]"
  refine' log_base2_square _
  refine' log_base2_half _;
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `weaken #[[expr 509/500], [expr 1021/1000]]"
  refine' log_base2_square _
  norm_num1
  exact log_base2_end (by norm_num1) (by norm_num1) (by norm_num1) (by norm_num1)

theorem logb_two_xValue2_interval : logb 2 xValue2 ∈ Icc (-0.24246 : ℝ) (-0.242435) :=
  ⟨logb_approx_second.1.le, logb_approx_second.2.le⟩

theorem logb_two_xValue3_interval : logb 2 xValue3 ∈ Icc (-2.69257 : ℝ) (-2.69251) :=
  ⟨logb_approx_third.1.le, logb_approx_third.2.le⟩

-- 0.6214571360946745562130177514792899408284023668639053254437869822...
-- 0.6214572992392223161453930684699915469146238377007607776838546069...
-- lemma bin_ent_calc : bin_ent 2 (1 / (2 - 0.817)) ∈ Icc (0.621456 : ℝ) 0.621458 :=
theorem binEnt_calc : binEnt 2 (1 / (2 - 0.817)) ∈ Icc (0.6214 : ℝ) 0.6214711 :=
  by
  rw [binEnt]
  refine'
    interval_end
      (sub_interval
        (hMul_interval_of_neg const_interval logb_two_xValue2_interval (by norm_num1)
          (by norm_num1))
        (hMul_interval_of_pos_neg const_interval logb_two_xValue3_interval (by norm_num1)
          (by norm_num1)))
      (by norm_num1) (by norm_num1)

end Values

open Real SimpleGraph

-- this expression is nicer to compare to g
/-- the special case of g on the line -/
noncomputable def g' (y : ℝ) :=
  logb 2 (5 / 2) + (3 / 5 * y + 0.5454) * logb 2 (5 / 3) +
    y * logb 2 ((y + 2727 / 8000) / (25 / 16 * y))

theorem g_line {x y : ℝ} (h : x = 3 / 5 * y + 0.5454) : g x y = g' y :=
  by
  subst x
  rw [g_eq, g']
  rcases eq_or_ne y 0 with (rfl | hy)
  · rw [MulZeroClass.zero_mul, MulZeroClass.zero_mul]
  congr 3
  field_simp [hy]
  ring_nf

-- for eval
theorem g'_eq1 {y : ℝ} (hy : 0 ≤ y) :
    g' y =
      (1.5454 - 7 / 5 * y) * logb 2 5 - (0.5454 + 3 / 5 * y) * logb 2 3 +
            y * logb 2 ((y + 2727 / 8000) / y) +
          4 * y -
        1 :=
  by
  rw [g', mul_comm (25 / 16) y, ← div_div, logb_div, logb_div, logb_base two_pos one_lt_two.ne']
  rotate_left
  · norm_num1
  · norm_num1
  · norm_num1
  · norm_num1
  rcases eq_or_lt_of_le hy with (rfl | hy₀)
  · ring_nf
  have : logb 2 (25 / 16) = 2 * logb 2 5 - 4 :=
    by
    have : (25 / 16 : ℝ) = 5 ^ 2 / 2 ^ 4 := by norm_num1
    rw [this, logb_div, _root_.logb_pow, _root_.logb_pow, logb_base]
    all_goals norm_num
  rw [logb_div, this]
  · ring_nf
  · positivity
  · norm_num1

-- for diff
theorem g'_eq2 {y : ℝ} (hy : 0 ≤ y) :
    g' y =
      1.5454 * logb 2 5 - 0.5454 * logb 2 3 - 1 + y * (4 - 7 / 5 * logb 2 5 - 3 / 5 * logb 2 3) +
        y * (logb 2 (y + 2727 / 8000) - logb 2 y) :=
  by
  rw [g'_eq1 hy]
  rcases eq_or_lt_of_le hy with (rfl | hy₀)
  · simp
  have : y + 2727 / 8000 ≠ 0 := by linarith
  rw [logb_div this hy₀.ne']
  ring_nf

theorem continuous_g' : ContinuousOn g' (Set.Ici 0) :=
  by
  refine' ContinuousOn.congr _ fun y => g'_eq2
  refine' ContinuousOn.add (Continuous.continuousOn (by continuity)) _
  simp only [mul_sub]
  refine'
    (continuous_on_id.mul (ContinuousOn.logb (continuous_on_id.add _) _)).sub
      logb_mul_continuous.continuous_on
  · exact continuousOn_const
  intro x hx
  rw [mem_Ici] at hx 
  dsimp
  linarith

/-- an expression for the derivative of g' which is convenient to differentiate -/
noncomputable def g'Deriv (y : ℝ) : ℝ :=
  4 - 7 / 5 * logb 2 5 - 3 / 5 * logb 2 3 +
    (logb 2 (y + 2727 / 8000) - logb 2 y - 2727 / 8000 / log 2 / (y + 2727 / 8000))

/-- an expression for the derivative of g' which is convenient to evaluate -/
noncomputable def g'DerivAlt (y : ℝ) : ℝ :=
  4 - 7 / 5 * logb 2 5 - 3 / 5 * logb 2 3 +
    (logb 2 ((y + 2727 / 8000) / y) - 2727 / 8000 / (y + 2727 / 8000) * (1 / log 2))

-- for diff
theorem hasDerivAt_g' {y : ℝ} (hy : 0 < y) : HasDerivAt g' (g'Deriv y) y :=
  by
  have hy5 : y + 2727 / 8000 ≠ 0 := by linarith
  have h₁ :
    HasDerivAt
      (fun y =>
        1.5454 * logb 2 5 - 0.5454 * logb 2 3 - 1 + y * (4 - 7 / 5 * logb 2 5 - 3 / 5 * logb 2 3) +
          y * (logb 2 (y + 2727 / 8000) - logb 2 y))
      (4 - 7 / 5 * logb 2 5 - 3 / 5 * logb 2 3 +
        (1 * (logb 2 (y + 2727 / 8000) - logb 2 y) +
          y * (1 / ((y + 2727 / 8000) * log 2) - 1 / (y * log 2))))
      y :=
    by
    refine' ((hasDerivAt_mul_const _).const_add _).add ((hasDerivAt_id' y).mul _)
    refine' (((hasDerivAt_id' y).AddConst _).logb _).sub (has_deriv_at_logb hy.ne')
    linarith
  have h₂ :
    4 - 7 / 5 * logb 2 5 - 3 / 5 * logb 2 3 +
        (1 * (logb 2 (y + 2727 / 8000) - logb 2 y) +
          y * (1 / ((y + 2727 / 8000) * log 2) - 1 / (y * log 2))) =
      g'Deriv y :=
    by
    rw [one_mul, mul_sub, mul_one_div, mul_one_div, ← div_div y y, div_self hy.ne', ← div_div, ←
      sub_div, div_sub' _ _ _ hy5, mul_one, ← sub_sub, sub_self, zero_sub, div_div,
      mul_comm _ (log 2), neg_div, ← sub_eq_add_neg, ← div_div, g'Deriv]
  rw [← h₂]
  have : Set.EqOn g' _ (Set.Ici 0) := fun y hy => g'_eq2 hy
  refine' h₁.congr_of_eventually_eq (eq_on.eventually_eq_of_mem this _)
  exact Ici_mem_nhds hy

theorem g'DerivAlt_eq {y : ℝ} (hy : 0 < y) : g'DerivAlt y = g'Deriv y :=
  by
  have hy5 : y + 2727 / 8000 ≠ 0 := by linarith
  rw [g'DerivAlt, g'Deriv, logb_div hy5 hy.ne']
  congr 2
  rw [div_mul_div_comm, div_div, mul_one, mul_comm]

theorem hasDerivAt_g'Deriv {y : ℝ} (hy : 0 < y) :
    HasDerivAt g'Deriv (-(1 / log 2) * (7436529 / 64000000) / (y * (y + 2727 / 8000) ^ 2)) y :=
  by
  have hy5 : y + 2727 / 8000 ≠ 0 := by linarith
  have :
    HasDerivAt g'Deriv
      (1 / ((y + 2727 / 8000) * log 2) - 1 / (y * log 2) -
        (0 * (y + 2727 / 8000) - 2727 / 8000 / log 2 * 1) / (y + 2727 / 8000) ^ 2)
      y :=
    (((((hasDerivAt_id' y).AddConst _).logb hy5).sub (has_deriv_at_logb hy.ne')).sub
          ((hasDerivAt_const _ _).div ((hasDerivAt_id' y).AddConst _) hy5)).const_add
      _
  convert this using 1
  have hy6 : y * 8000 + 2727 ≠ 0 := by linarith
  field_simp [hy6, hy.ne', (log_pos one_lt_two).ne']
  ring

theorem strictAntiOn_g'Deriv : StrictAntiOn g'Deriv (Set.Ioi 0) :=
  by
  refine' Convex.strictAntiOn_of_hasDerivAt_neg (convex_Ioi 0) (fun y => hasDerivAt_g'Deriv) _
  rw [interior_Ioi]
  rintro x (hx : 0 < x)
  refine' mul_neg_of_neg_of_pos _ (by positivity)
  simp only [one_div, neg_mul, Right.neg_neg_iff]
  have := log_pos one_lt_two
  positivity

-- lemma (1.5454 - 7 / 5 * y) * logb 2 5 - (0.5454 + 3 / 5 * y) * logb 2 3 +
--     y * logb 2 ((y + 2727 / 8000) / y) + 4 * y - 1
theorem g'_eval_max : g' 0.4339 ∈ Icc (1.99928 : ℝ) 1.99929 :=
  by
  rw [g'_eq1]
  swap
  · norm_num1
  rw [add_sub_assoc]
  refine'
    interval_end
      (add_interval
        (add_interval
          (sub_interval
            (hMul_interval const_interval logb_two_five_interval (by norm_num1) (by norm_num1))
            (hMul_interval const_interval logb_two_three_interval (by norm_num1) (by norm_num1)))
          (hMul_interval const_interval logb_two_xValue_interval (by norm_num1) (by norm_num1)))
        const_interval)
      (by norm_num1) (by norm_num1)

theorem g_deriv_eval_max : g'Deriv 0.4339 ∈ Icc (0. : ℝ) 1e-6 :=
  by
  rw [← g'DerivAlt_eq]
  swap; · norm_num1
  rw [g'DerivAlt]
  refine'
    interval_end
      (add_interval
        (sub_interval
          (sub_interval const_interval
            (hMul_interval const_interval logb_two_five_interval (by norm_num1) (by norm_num1)))
          (hMul_interval const_interval logb_two_three_interval (by norm_num1) (by norm_num1)))
        (sub_interval logb_two_xValue_interval
          (hMul_interval const_interval one_div_log_two_interval (by norm_num1) (by norm_num1))))
      (by norm_num1) (by norm_num1)

theorem claim_a2_aux {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 0.75) : g' y < 1.9993 :=
  by
  cases le_total y 0.4339
  · have hdif : DifferentiableOn ℝ g' (interior (Icc 0 (4339 / 10000))) :=
      by
      rw [interior_Icc]
      intro x hx
      exact (hasDerivAt_g' hx.1).DifferentiableAt.DifferentiableWithinAt
    have hder : ∀ x ∈ interior (Icc (0 : ℝ) 0.4339), 0. ≤ deriv g' x :=
      by
      rw [interior_Icc]
      rintro x ⟨hx₀, hx₁⟩
      rw [(hasDerivAt_g' hx₀).deriv]
      refine' (strictAntiOn_g'Deriv hx₀ (by norm_num) hx₁).le.trans' _
      exact g_deriv_eval_max.1
    have :=
      Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc 0 0.4339)
        (continuous_g'.mono Icc_subset_Ici_self) hdif hder y ⟨hy.1, h⟩ 0.4339 (by norm_num) h
    rw [le_sub_iff_add_le] at this 
    replace this := this.trans g'_eval_max.2
    linarith only [this, h]
  · have h₁ : Icc (4339 / 10000 : ℝ) 0.75 ⊆ Ici 0 := by rw [Icc_subset_Ici_iff] <;> norm_num1
    have h₂ : Ioo (4339 / 10000 : ℝ) 0.75 ⊆ Ioi 0 :=
      by
      rintro x ⟨hx, _⟩
      rw [mem_Ioi]
      linarith only [hx]
    have hdif : DifferentiableOn ℝ g' (interior (Icc (4339 / 10000) 0.75)) :=
      by
      intro x hx
      rw [interior_Icc] at hx 
      exact (hasDerivAt_g' (h₂ hx)).DifferentiableAt.DifferentiableWithinAt
    have hder : ∀ x ∈ interior (Icc (4339 / 10000 : ℝ) 0.75), deriv g' x ≤ 1e-6 :=
      by
      rintro x hx
      rw [interior_Icc] at hx 
      rw [(hasDerivAt_g' (h₂ hx)).deriv]
      refine' (strictAntiOn_g'Deriv (by norm_num) (h₂ hx) hx.1).le.trans _
      exact g_deriv_eval_max.2
    have :=
      Convex.image_sub_le_mul_sub_of_deriv_le (convex_Icc 0.4339 0.75) (continuous_g'.mono h₁) hdif
        hder 0.4339 (by norm_num) y ⟨h, hy.2⟩ h
    --   (continuous_g'.mono Icc_subset_Ici_self) hdif hder y ⟨hy.1, h⟩ 0.4339 (by norm_num) h,
    rw [sub_le_comm] at this 
    replace this := this.trans g'_eval_max.2
    linarith only [this, hy.2]

theorem claim_a2 {x y : ℝ} (hy : y ∈ Icc (0 : ℝ) 0.75) (h : x = 3 / 5 * y + 0.5454) :
    SimpleGraph.g x y < 1.9993 := by
  rw [g_line h]
  exact claim_a2_aux hy

/-- the function `f` on the line -/
noncomputable def f' (x : ℝ) : ℝ :=
  8 / 3 * x - 0.909 + (2 - x) * binEnt 2 (1 / (2 - x))

theorem continuous_f' : Continuous f' :=
  by
  refine' Continuous.add (by continuity) _
  exact continuous_on_mul_bin_ent_inv.comp (continuous_const.sub continuous_id')

theorem hasDerivAt_f' {x : ℝ} (hx₁ : x ≠ 1) (hx₂ : x ≠ 2) :
    HasDerivAt f' (8 / 3 + logb 2 ((1 - x) / (2 - x))) x :=
  by
  have : HasDerivAt f' (_ + logb 2 ((1 - x) / (2 - x))) x :=
    (((hasDerivAt_id' x).const_mul _).sub_const _).add (f1_deriv_helper hx₁ hx₂)
  rwa [mul_one] at this 

theorem f_inner_eq {x y : ℝ} (h : x = 3 / 5 * y + 0.5454) :
    x + y + (2 - x) * binEnt 2 (1 / (2 - x)) = f' x :=
  by
  have : y = 5 / 3 * x - 0.909 := by linarith only [h]
  rw [this, f', add_left_inj]
  ring_nf

theorem strictMonoOn_f' : StrictMonoOn f' (Icc 0 0.75) :=
  by
  refine' Convex.strictMonoOn_of_deriv_pos (convex_Icc _ _) _ _
  · exact continuous_f'.continuous_on
  rw [interior_Icc]
  rintro x ⟨hx₀, hx₁⟩
  have h₁ : 0 < 1 - x := by linarith only [hx₁]
  have h₂ : 0 < 2 - x := by linarith only [h₁]
  rw [(hasDerivAt_f' _ _).deriv]
  rotate_left
  · linarith only [h₁]
  · linarith only [h₁]
  have : 0.2 ≤ (1 - x) / (2 - x) := by
    rw [le_div_iff h₂]
    linarith only [hx₁]
  have : -logb 2 5 ≤ logb 2 ((1 - x) / (2 - x)) :=
    by
    rw [← logb_inv, ← one_div]
    exact _root_.logb_le_logb_of_le (by norm_num1) (by norm_num1) this
  replace this := this.trans' (neg_le_neg logb_two_five_interval.2)
  refine' (add_le_add_left this _).trans_lt' _
  norm_num1

theorem f'_max : f' 0.75 < 1.994 :=
  by
  have : logb 2 (4 / 5) = 2 - logb 2 5 :=
    by
    rw [logb_div, (by norm_num1 : (4 : ℝ) = 2 ^ 2), _root_.logb_pow, logb_base]
    · rw [Nat.cast_two, mul_one]
    · norm_num1
    · norm_num1
    · norm_num1
    · norm_num1
  rw [f', binEnt]
  norm_num1
  rw [this, one_div, logb_inv]
  have : logb 2 5 < 2.3224 := logb_two_five_interval.2.trans_lt (by norm_num1)
  ring_nf
  linarith only [this]

theorem claim_a3 {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 0.75) (h : x = 3 / 5 * y + 0.5454) :
    f1 x y < 1.9993 := by
  rw [f1, f_inner_eq h]
  refine' (strict_mono_on_f'.monotone_on hx (right_mem_Icc.2 (by norm_num1)) hx.2).trans_lt _
  exact f'_max.trans_le (by norm_num1)

/-- an expression for f2 on the line -/
noncomputable def f2' (x : ℝ) : ℝ :=
  f' x - 1 / (log 2 * 40) * (1 - 1 / (2 - x))

theorem f2'_eq {x : ℝ} : f2' x = f' x - 1 / log 2 * (1 / 40 * (1 - 1 / (2 - x))) := by
  rw [f2', ← one_div_mul_one_div, mul_assoc]

/-- an expression for the derivative of f2 -/
noncomputable def f2'Deriv (x : ℝ) : ℝ :=
  8 / 3 + logb 2 ((1 - x) / (2 - x)) + 1 / (log 2 * 40) * (1 / (2 - x) ^ 2)

theorem hasDerivAt_f2' {x : ℝ} (hx : x < 1) : HasDerivAt f2' (f2'Deriv x) x :=
  by
  have hx2 : x < 2 := by linarith only [hx]
  have : HasDerivAt f2' (8 / 3 + logb 2 ((1 - x) / (2 - x)) - _) x :=
    (hasDerivAt_f' hx.ne hx2.ne).sub (((hasDerivAt_const _ _).sub (f_deriv_aux hx2.ne)).const_mul _)
  convert this using 1
  rw [f2'Deriv, zero_sub, mul_neg, sub_neg_eq_add]

-- for diff
theorem f2_deriv'_eq {x : ℝ} :
    f2'Deriv x = 8 / 3 + logb 2 (1 - x) - logb 2 (2 - x) + 1 / (log 2 * 40) * ((2 - x) ^ 2)⁻¹ := by
  rw [f2'Deriv, important_rewrite2, one_div, one_div, add_sub_assoc]

-- for eval
theorem f2_deriv'_eq2 {x : ℝ} :
    f2'Deriv x = 8 / 3 + logb 2 (1 - 1 / (2 - x)) + 1 / log 2 * (1 / (40 * (2 - x) ^ 2)) := by
  rw [f2'Deriv, important_rewrite', one_div_mul_one_div, one_div_mul_one_div, mul_assoc]

-- 20 y^2 - 79 y + 79
-- 20 y ^ 2 - 80 y + 80 - (1 - y)
-- 20 (y ^ 2 - 4 y + 4) - (1 - y)
-- (1 - y) - 20 (2 - y) ^ 2
theorem hasDerivAt_f2'Deriv {y : ℝ} (hy : y < 1) :
    HasDerivAt (fun x => f2'Deriv x)
      ((1 - y - 20 * (2 - y) ^ 2) / (20 * (2 - y) ^ 3 * (1 - y) * log 2)) y :=
  by
  simp only [f2_deriv'_eq]
  have hy2 : y < 2 := hy.trans_le one_le_two
  have :
    HasDerivAt
      (fun x => 8 / 3 + logb 2 (1 - x) - logb 2 (2 - x) + 1 / (log 2 * 40) * ((2 - x) ^ 2)⁻¹)
      ((0 - 1) / ((1 - y) * log 2) - (0 - 1) / ((2 - y) * log 2) +
        1 / (log 2 * 40) * (-(↑2 * (2 - y) ^ (2 - 1) * -1) / ((2 - y) ^ 2) ^ 2))
      y :=
    by
    refine'
      (((((hasDerivAt_const _ _).sub (hasDerivAt_id' _)).logb _).const_add _).sub
            (((hasDerivAt_const _ _).sub (hasDerivAt_id' _)).logb _)).add
        (HasDerivAt.const_mul _ _)
    · exact sub_ne_zero_of_ne hy.ne'
    · exact sub_ne_zero_of_ne hy2.ne'
    refine' (((hasDerivAt_id' _).const_sub _).pow _).inv _
    simp only [Ne.def, pow_eq_zero_iff, zero_lt_bit0, Nat.lt_one_iff, sub_eq_zero, hy2.ne',
      not_false_iff]
  convert this using 1
  -- rw [nat.cast_two],
  field_simp [(log_pos one_lt_two).ne', (sub_pos_of_lt hy).ne', (sub_pos_of_lt hy2).ne']
  ring_nf

theorem strictAntiOn_f2'Deriv : StrictAntiOn f2'Deriv (Set.Ioo 0 1) :=
  by
  refine'
    Convex.strictAntiOn_of_hasDerivAt_neg (convex_Ioo 0 1) (fun y hy => hasDerivAt_f2'Deriv hy.2) _
  rw [interior_Ioo]
  rintro x ⟨hx₀, hx₁⟩
  suffices 1 - x - 20 * (2 - x) ^ 2 < 0
    by
    refine' div_neg_of_neg_of_pos this _
    have : 0 < 1 - x := sub_pos_of_lt hx₁
    have : 0 < 2 - x := by linarith only [hx₁]
    have := log_pos one_lt_two
    positivity
  nlinarith

-- deriv = -0.0000960352
-- 1.9992712424
-- lower bound here doesn't matter
theorem f2'_eval_max : f2' 0.817 ∈ Icc (0 : ℝ) 1.9992877 :=
  by
  rw [f2'_eq, f']
  refine'
    interval_end
      (sub_interval
        (add_interval const_interval
          (hMul_interval const_interval binEnt_calc (by norm_num1) (by norm_num1)))
        (hMul_interval one_div_log_two_interval const_interval (by norm_num1) (by norm_num1)))
      (by norm_num1) (by norm_num1)

-- sorry
theorem f2'Deriv_eval_max : f2'Deriv 0.817 ∈ Icc (-15e-5 : ℝ) 5e-5 :=
  by
  rw [f2_deriv'_eq2]
  refine'
    interval_end
      (add_interval (add_interval const_interval logb_two_xValue3_interval)
        (hMul_interval one_div_log_two_interval const_interval (by norm_num1) (by norm_num1)))
      (by norm_num) (by norm_num1)

theorem claim_a4_aux {x : ℝ} (hx : x ∈ Ico (0.75 : ℝ) 1) : f2' x < 1.9993 :=
  by
  cases le_total x 0.817
  · have hdif : DifferentiableOn ℝ f2' (Icc 0.75 0.817) :=
      by
      intro x hx
      refine' (hasDerivAt_f2' _).DifferentiableAt.DifferentiableWithinAt
      exact hx.2.trans_lt (by norm_num1)
    have hder : ∀ x ∈ interior (Icc (0.75 : ℝ) 0.817), -15e-5 ≤ deriv f2' x :=
      by
      rw [interior_Icc]
      rintro x ⟨hx₀, hx₁⟩
      rw [(hasDerivAt_f2' (hx₁.trans_le (by norm_num1))).deriv]
      refine' (strictAntiOn_f2'Deriv _ (by norm_num) hx₁).le.trans' f2'Deriv_eval_max.1
      exact ⟨hx₀.trans' (by norm_num1), hx₁.trans (by norm_num1)⟩
    have :=
      Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc 0.75 0.817) hdif.continuous_on
        (hdif.mono interior_subset) hder _ ⟨hx.1, h⟩ 0.817 (by norm_num) h
    rw [le_sub_iff_add_le] at this 
    replace this := this.trans f2'_eval_max.2
    linarith only [this, hx.1]
  · have hdif : DifferentiableOn ℝ f2' (Ico 0.817 1) :=
      by
      intro x hx
      exact (hasDerivAt_f2' hx.2).DifferentiableAt.DifferentiableWithinAt
    have hder : ∀ x ∈ interior (Ico (0.817 : ℝ) 1), deriv f2' x ≤ 5e-5 :=
      by
      rintro x hx
      rw [interior_Ico] at hx 
      rw [(hasDerivAt_f2' hx.2).deriv]
      refine' (strictAntiOn_f2'Deriv (by norm_num) _ hx.1).le.trans f2'Deriv_eval_max.2
      exact ⟨hx.1.trans' (by norm_num1), hx.2⟩
    have :=
      Convex.image_sub_le_mul_sub_of_deriv_le (convex_Ico 0.817 1) hdif.continuous_on
        (hdif.mono interior_subset) hder 0.817 (by norm_num) _ ⟨h, hx.2⟩ h
    rw [sub_le_comm] at this 
    replace this := this.trans f2'_eval_max.2
    linarith only [this, hx.2]

theorem claim_a4 {x y : ℝ} (hx : x ∈ Icc (0.75 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 0.75)
    (h : x = 3 / 5 * y + 0.5454) : f2 x y < 1.9993 :=
  by
  have hx09 : x ≤ 0.9954 := by linarith only [h, hy.2]
  have hx1 : x < 1 := hx09.trans_lt (by norm_num1)
  have hx2 : x ≠ 2 := by linarith only [hx1]
  rw [f2, f_inner_eq h, ← important_rewrite hx2, ← f2']
  exact claim_a4_aux ⟨hx.1, hx1⟩

