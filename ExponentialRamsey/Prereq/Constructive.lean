/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ExponentialRamsey.Prereq.Ramsey
import Mathlib.Combinatorics.Pigeonhole

/-!
# Constructive lower bounds on Ramsey numbers
-/


namespace SimpleGraph

namespace Product

open Finset

/--
an explicit two-labelling of [k] x [l] which should, by construction, not contain an 0-labelled k+1
or 1-labelled l+1 clique
-/
def myLabelling (k l : ℕ) : TopEdgeLabelling (Fin k × Fin l) (Fin 2) :=
  TopEdgeLabelling.mk (fun x y _ => if x.2 = y.2 then 0 else 1) fun x y _ => by
    simp only [@eq_comm (Fin l)]

theorem isRamseyValid_myLabelling {k l : ℕ} : ¬IsRamseyValid (Fin k × Fin l) ![k + 1, l + 1] :=
  by
  rw [isRamseyValid_iff_eq]
  intro h
  obtain ⟨m, hm⟩ := h (myLabelling _ _)
  simp only [Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hm
  rcases hm with (⟨hm, hm'⟩ | ⟨hm, hm'⟩)
  · have h₁ : ∀ i ∈ m, Prod.fst i ∈ (Finset.univ : Finset (Fin k)) := by simp
    have h₂ : (Finset.univ : Finset (Fin k)).card * 1 < m.card :=
      by
      rw [mul_one, ← hm', Finset.card_fin]
      simp
    obtain ⟨i, -, hi⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to h₁ h₂
    simp only [Finset.one_lt_card_iff, Finset.mem_filter, Prod.exists, and_assoc] at hi
    obtain ⟨a, b, c, d, habm, rfl, hcdm, rfl, hi⟩ := hi
    have := hm habm hcdm hi
    simp only [myLabelling, TopEdgeLabelling.mk_get] at this
    simp only [Ne.eq_def, Prod.mk_inj, true_and] at hi
    simp [if_neg hi] at this
  · have h₁ : ∀ i ∈ m, Prod.snd i ∈ (Finset.univ : Finset (Fin l)) := by simp
    have h₂ : (Finset.univ : Finset (Fin l)).card * 1 < m.card :=
      by
      rw [mul_one, ← hm', Finset.card_fin]
      simp
    obtain ⟨i, -, hi⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to h₁ h₂
    simp only [Finset.one_lt_card_iff, Finset.mem_filter, Prod.exists, and_assoc] at hi
    obtain ⟨a, b, c, d, habm, rfl, hcdm, rfl, hi⟩ := hi
    have := hm habm hcdm hi
    simp only [myLabelling, TopEdgeLabelling.mk_get] at this
    simp only [Ne.eq_def, Prod.mk_inj] at hi
    simp at this

theorem ramsey_product_bound (k l : ℕ) : k * l < ramseyNumber ![k + 1, l + 1] :=
  by
  have := @isRamseyValid_myLabelling k l
  rwa [← ramseyNumber_le_iff, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, not_le] at this

/--
an explicit two-labelling of α x [l] which should, by construction, not contain an 0-labelled |α|
clique or 1-labelled l+2 clique
-/
def myOtherLabelling' (α : Type*) [DecidableEq α] (l : ℕ) (a b : α) :
    TopEdgeLabelling (α × Fin l) (Fin 2) :=
  TopEdgeLabelling.mk
    (fun x y _ =>
      if
          x.1 = y.1 ∨
            (s(x.1, y.1) : Sym2 α) = s(a, b) ∧ x.2 = y.2 ∨
              (s(x.1, y.1) : Sym2 α) ≠ s(a, b) ∧ x.2 ≠ y.2 then
        1
      else 0)
    (by
      intro x y _
      refine if_congr ?_ rfl rfl
      rw [Sym2.eq_swap, Ne.eq_def y.2, @eq_comm _ y.1, @eq_comm _ y.2])

theorem myOtherLabelling_swap' (α : Type*) [DecidableEq α] (l : ℕ) (a b : α) :
    myOtherLabelling' α l a b = myOtherLabelling' α l b a :=
  by
  refine TopEdgeLabelling.ext_get ?_
  intro x y h
  simp only [myOtherLabelling', TopEdgeLabelling.mk_get]
  refine if_congr ?_ rfl rfl
  rw [@Sym2.eq_swap _ a]

open scoped BigOperators

theorem isRamseyValid_myOtherLabelling'_zero {α : Type*} [Fintype α] [DecidableEq α] {x y : α}
    {l : ℕ} {m : Finset (α × Fin l)} (z : α) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ¬((myOtherLabelling' α l x y).MonochromaticOf m 0 ∧ Fintype.card α = m.card) :=
  by
  rintro ⟨hm, hm'⟩
  have : ∀ i ∈ (Finset.univ : Finset α), (m.filter fun x : _ × _ => x.fst = i).card ≤ 1 :=
    by
    rintro i -
    rw [Finset.card_le_one]
    simp only [Finset.mem_filter, and_imp, Prod.forall]
    rintro a b hab rfl a' b' hab' rfl
    by_contra!
    have := hm hab hab' this
    rw [myOtherLabelling', TopEdgeLabelling.mk_get] at this
    simp only [true_or, if_true, Fin.one_eq_zero_iff, Nat.succ_succ_ne_one] at this
  have : ∀ i ∈ (Finset.univ : Finset α), (Finset.filter (fun x : _ × Fin l => x.fst = i) m).card = 1 :=
    by
    rw [← Finset.sum_eq_sum_iff_of_le this, ← Finset.card_eq_sum_ones, Finset.card_univ,
        ← Finset.card_eq_sum_card_fiberwise, ← hm']
    intro x xm; simp only [Finset.coe_univ, Set.mem_univ]
  have : ∀ i : α, ∃ a : α × Fin l, a ∈ m ∧ a.fst = i :=
    by
    intro i
    rw [← Finset.filter_nonempty_iff, ← Finset.card_pos, this i (Finset.mem_univ _)]
    simp only [Nat.lt_one_iff]
  have h' : ∀ i : α, ∃ j : Fin l, (i, j) ∈ m :=
    by
    intro i
    obtain ⟨⟨a, b⟩, c, rfl⟩ := this i
    exact ⟨b, c⟩
  choose f hf using h'
  have h₁ :
    ∀ {x y : α},
      x ≠ y → (myOtherLabelling' α l x y).MonochromaticOf m 0 → ∀ i, i ≠ x → f i = f y :=
    by
    intro x y _ hm i hi₁
    by_contra!
    have : (i, f i) ≠ (y, f y) :=
      by
      rw [Ne.eq_def, Prod.mk_inj, not_and_or]
      exact Or.inr this
    have := hm (hf _) (hf _) this
    rw [myOtherLabelling', TopEdgeLabelling.mk_get, if_pos] at this
    · simp only [Fin.one_eq_zero_iff, Nat.succ_succ_ne_one] at this
    refine Or.inr (Or.inr ⟨?_, ‹_›⟩)
    dsimp
    rw [Sym2.congr_left]
    exact hi₁
  have h₂ : ∀ i, i ≠ x → f i = f y := h₁ hxy hm
  have h₃ : ∀ i, i ≠ y → f i = f x := by
    refine h₁ hxy.symm ?_
    rwa [myOtherLabelling_swap']
  have h₄ : f x ≠ f y := by
    intro h'
    have : (x, f x) ≠ (y, f y) := by
      simp only [hxy, Ne.eq_def, Prod.mk_inj, false_and, not_false_iff]
    have := hm (hf _) (hf _) this
    rw [myOtherLabelling', TopEdgeLabelling.mk_get, if_pos] at this
    · simp only [Fin.one_eq_zero_iff, Nat.succ_succ_ne_one] at this
    exact Or.inr (Or.inl ⟨rfl, h'⟩)
  refine h₄ ?_
  rw [← h₂ z hxz.symm, h₃ z hyz.symm]

theorem isRamseyValid_myOtherLabelling_one {α : Type*} [DecidableEq α] [Finite α] {l : ℕ}
    {m : Finset (α × Fin l)} (x y : α) (h : x ≠ y) :
    ¬((myOtherLabelling' α l x y).MonochromaticOf m 1 ∧ l + 2 = m.card) :=
  by
  cases nonempty_fintype α
  rintro ⟨hm, hm'⟩
  let f' : α → Finset (α × Fin l) := fun i => m.filter fun x => x.1 = i
  -- let s₁₂ : finset α := {x}ᶜ,
  -- let s₀₂ : finset α := {y}ᶜ,
  have h₀ : ∀ x : α, ((({x}ᶜ : Finset α).biUnion f').image Prod.snd).card ≤ l :=
    by
    intro x
    refine (Finset.card_le_univ _).trans ?_
    rw [Fintype.card_fin]
  have h₀' :
    ∀ x y,
      x ≠ y →
        (myOtherLabelling' α l x y).MonochromaticOf m 1 →
          Set.InjOn Prod.snd (({x}ᶜ : Finset α).biUnion f' : Set (α × Fin l)) :=
    by
    intro x y _ hm
    simp only [Set.InjOn, Finset.mem_coe, Finset.mem_biUnion, forall_exists_index, Finset.mem_compl,
      Finset.mem_singleton, Prod.forall, Finset.mem_filter, and_imp, f']
    rintro a b _ ha hab rfl a' _ _ ha' hab' rfl rfl
    by_contra!
    have h := hm hab hab' this
    rw [myOtherLabelling', TopEdgeLabelling.mk_get] at h
    simp only [Ne.eq_def, Prod.mk_inj, and_true] at this
    simp [this, ha, ha'] at h
  have hx : ((({x}ᶜ : Finset α).biUnion f').image Prod.snd).card ≤ l := h₀ _
  have hy : ((({y}ᶜ : Finset α).biUnion f').image Prod.snd).card ≤ l := h₀ _
  rw [Finset.card_image_of_injOn (h₀' _ _ h hm)] at hx
  have hm_alt : (myOtherLabelling' α l y x).MonochromaticOf m 1 := by
    rwa [myOtherLabelling_swap']
  rw [Finset.card_image_of_injOn (h₀' _ _ h.symm hm_alt)] at hy
  have : ∀ i, f' i ∪ ({i}ᶜ : Finset α).biUnion f' = m :=
    by
    intro i
    rw [← Finset.biUnion_insert, Finset.insert_compl_self, Finset.biUnion_filter_eq_of_maps_to]
    simp
  suffices m.card ≤ l + 1 by
    rw [← hm'] at this
    norm_num at this
  cases' le_or_gt (f' x).card 1 with hx' hx'
  · rw [← this x, Finset.union_comm]
    exact (Finset.card_union_le _ _).trans (add_le_add hx hx')
  clear hm_alt
  have f'y : f' y = ∅ := by
    rw [Finset.one_lt_card] at hx'
    simp only [Finset.mem_filter, Prod.exists, Ne.eq_def, and_assoc, f'] at hx'
    obtain ⟨_, b, hxb, rfl, x, b', hxb', rfl, h'⟩ := hx'
    rw [Finset.eq_empty_iff_forall_notMem]
    simp only [Prod.forall, Finset.mem_filter, not_and, f']
    rintro y b'' hab'' rfl
    apply h'
    have : (x, b) ≠ (y, b'') := by
      simp only [Ne.eq_def, Prod.mk_inj, h, false_and, not_false_iff]
    have := hm hxb hab'' this
    rw [myOtherLabelling', TopEdgeLabelling.mk_get] at this
    simp only [true_and, Ne.eq_def, not_true, false_and, or_false, ite_eq_left_iff,
      Fin.zero_eq_one_iff, Nat.succ_succ_ne_one, h, false_or, imp_false, Classical.not_not] at this
    cases this
    have : (x, b') ≠ (y, b) := by
      simp only [Ne.eq_def, Prod.mk_inj, h, false_and, not_false_iff]
    have := hm hxb' hab'' this
    rw [myOtherLabelling', TopEdgeLabelling.mk_get] at this
    simp only [true_and, Ne.eq_def, not_true, false_and, or_false, ite_eq_left_iff,
      Fin.zero_eq_one_iff, Nat.succ_succ_ne_one, h, false_or, imp_false, Classical.not_not] at this
    rw [this]
  rw [← this y, f'y, Finset.empty_union]
  exact hy.trans (by simp)

theorem isRamseyValid_myOtherLabelling {k l : ℕ} :
    ¬IsRamseyValid (Fin (k + 3) × Fin l) ![k + 3, l + 2] :=
  by
  rw [isRamseyValid_iff_eq]
  intro h
  obtain ⟨m, hm⟩ := h (myOtherLabelling' _ _ 0 1)
  simp only [Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hm
  rcases hm with (hm | hm)
  · have :
      (myOtherLabelling' (Fin (k + 3)) l 0 1).MonochromaticOf m 0 ∧
        Fintype.card (Fin (k + 3)) = m.card :=
      by simpa using hm
    refine isRamseyValid_myOtherLabelling'_zero (2 : Fin (k + 3)) ?_ ?_ ?_ this
    all_goals exact ne_of_beq_false rfl -- was "decide"
  · refine isRamseyValid_myOtherLabelling_one _ _ ?_ hm
    norm_num

theorem ramsey_product_bound' (k l : ℕ) : (k + 3) * l < ramseyNumber ![k + 3, l + 2] :=
  by
  have := @isRamseyValid_myOtherLabelling k l
  rwa [← ramseyNumber_le_iff, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, not_le] at this

end Product

theorem sub_one_mul_sub_one_lt_ramseyNumber {k l : ℕ} (hk : k ≠ 0) (hl : l ≠ 0) :
    (k - 1) * (l - 1) < ramseyNumber ![k, l] :=
  by
  cases' k with k
  · simp at hk
  cases' l with l
  · simp at hl
  exact Product.ramsey_product_bound k l

theorem sub_one_mul_sub_one_le_ramseyNumber {k l : ℕ} : (k - 1) * (l - 1) ≤ ramseyNumber ![k, l] :=
  by
  cases' k
  · simp
  cases' l
  · simp
  refine (sub_one_mul_sub_one_lt_ramseyNumber ?_ ?_).le <;> simp

theorem mul_sub_two_lt_ramseyNumber {k l : ℕ} (hk : 3 ≤ k) (hl : l ≠ 0) :
    k * (l - 2) < ramseyNumber ![k, l] :=
  by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hk
  cases' l with l
  · simp at hl
  cases' l with l
  · rw [ramseyNumber_pair_swap, ramseyNumber_one_succ]
    simp
  exact Product.ramsey_product_bound' k l

theorem hMul_sub_two_le_ramseyNumber {k l : ℕ} (hk : 3 ≤ k) : k * (l - 2) ≤ ramseyNumber ![k, l] :=
  by
  cases l
  · simp
  refine (mul_sub_two_lt_ramseyNumber hk ?_).le
  simp

theorem left_lt_ramseyNumber_three {k : ℕ} (hk : 2 ≤ k) : k < ramseyNumber ![k, 3] :=
  by
  cases' k with k
  · simp at hk
  cases' k with k
  · norm_num at hk
  cases k
  · norm_num
  refine (mul_sub_two_lt_ramseyNumber ?_ ?_).trans_le' ?_
  · simp only [Nat.succ_le_succ_iff]
    exact Nat.zero_le _
  · norm_num
  · simp

theorem left_lt_ramseyNumber {k l : ℕ} (hk : 2 ≤ k) (hl : 3 ≤ l) : k < ramseyNumber ![k, l] :=
  (left_lt_ramseyNumber_three hk).trans_le (ramseyNumber.mono_two le_rfl hl)

theorem right_lt_ramseyNumber {k l : ℕ} (hk : 3 ≤ k) (hl : 2 ≤ l) : l < ramseyNumber ![k, l] := by
  rw [ramseyNumber_pair_swap]; exact left_lt_ramseyNumber hl hk

end SimpleGraph
