/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import ExponentialRamsey.Prereq.Mathlib.Analysis.SpecialFunctions.ExplicitStirling
import ExponentialRamsey.Prereq.RamseySmall
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Order.Partition.Finpartition
import Mathlib.Tactic.IntervalCases

/-!
# Asymptotic lower bounds on ramsey numbers by probabilistic arguments
-/


open Finset

namespace SimpleGraph

open scoped BigOperators

open Fintype (card)

variable {V : Type*} {G G₁ G₂ : SimpleGraph V}

theorem card_filter_not_diag {α : Type*} [Fintype α] [DecidableEq α] :
    (Finset.univ.filter fun a : Sym2 α => ¬Sym2.IsDiag a).card = (card α).choose 2 := by
  rw [← Sym2.card_subtype_not_diag, Fintype.card_subtype]

theorem edgeFinset_bot' [Fintype (edgeSet (⊥ : SimpleGraph V))] :
    (⊥ : SimpleGraph V).edgeFinset = ∅ := by simp [edgeFinset]

theorem edgeFinset_sup' [DecidableEq V] [Fintype (edgeSet G₁)]
    [Fintype (edgeSet G₂)] [Fintype (edgeSet (G₁ ⊔ G₂))] :
    (G₁ ⊔ G₂).edgeFinset = G₁.edgeFinset ∪ G₂.edgeFinset := by simp [edgeFinset]

theorem edgeFinset_inf' [DecidableEq V] [Fintype (edgeSet G₁)]
    [Fintype (edgeSet G₂)] [Fintype (edgeSet (G₁ ⊓ G₂))] :
    (G₁ ⊓ G₂).edgeFinset = G₁.edgeFinset ∩ G₂.edgeFinset := by simp [edgeFinset]

theorem edgeFinset_sdiff' [DecidableEq V] [Fintype (edgeSet G₁)]
    [Fintype (edgeSet G₂)] [Fintype (edgeSet (G₁ \ G₂))] :
    (G₁ \ G₂).edgeFinset = G₁.edgeFinset \ G₂.edgeFinset := by simp [edgeFinset]

theorem edgeFinset_top_card [Fintype V] [DecidableEq V] :
    (⊤ : SimpleGraph V).edgeFinset.card = (card V).choose 2 := by
  rw [edgeFinset_card, card_top_edgeSet]

theorem edgeFinset_card_le [Fintype V] [Fintype G.edgeSet] :
    G.edgeFinset.card ≤ (card V).choose 2 := by
  classical
  rw [← edgeFinset_top_card]
  exact card_le_card (edgeFinset_mono le_top)


theorem compl_edgeSet_eq :
    edgeSet (Gᶜ) = {x : Sym2 V | ¬x.IsDiag} \ edgeSet G := by
  rw [← edgeSet_top, ← edgeSet_sdiff, top_sdiff]

theorem compl_edgeSet_eq' :
    edgeSet G = {x : Sym2 V | ¬x.IsDiag} \ edgeSet (Gᶜ) := by
  rw [← edgeSet_top, ← edgeSet_sdiff, top_sdiff, compl_compl]

theorem compl_edgeFinset_eq [Fintype V] [DecidableEq V] [Fintype G.edgeSet] [Fintype Gᶜ.edgeSet] :
    Gᶜ.edgeFinset = (univ.filter fun a : Sym2 V => ¬Sym2.IsDiag a) \ G.edgeFinset := by
  refine coe_injective ?_
  rw [coe_edgeFinset, coe_sdiff, coe_edgeFinset, coe_filter_univ, compl_edgeSet_eq]

theorem compl_edgeFinset_eq' [Fintype V] [DecidableEq V] [Fintype G.edgeSet] [Fintype Gᶜ.edgeSet] :
    G.edgeFinset = (univ.filter fun a : Sym2 V => ¬Sym2.IsDiag a) \ Gᶜ.edgeFinset := by
  refine coe_injective ?_
  rw [coe_edgeFinset, coe_sdiff, coe_edgeFinset, coe_filter_univ, compl_edgeSet_eq']

theorem card_compl_edgeFinset_eq [Fintype V] [Fintype G.edgeSet]
    [Fintype Gᶜ.edgeSet] : Gᶜ.edgeFinset.card = (card V).choose 2 - G.edgeFinset.card := by
  classical
  rw [compl_edgeFinset_eq, card_sdiff, card_filter_not_diag]
  simp only [subset_iff, mem_edgeFinset, mem_filter, mem_univ, true_and]
  apply not_isDiag_of_mem_edgeSet

theorem card_edgeFinset_eq_sub_compl' [Fintype V] [Fintype G.edgeSet]
    [Fintype Gᶜ.edgeSet] : G.edgeFinset.card = (card V).choose 2 - Gᶜ.edgeFinset.card := by
  classical
  rw [compl_edgeFinset_eq', card_sdiff, card_filter_not_diag]
  simp only [subset_iff, mem_edgeFinset, mem_filter, mem_univ, true_and]
  apply not_isDiag_of_mem_edgeSet

variable {p : ℝ} {s : Finset (Sym2 V)}

/-- a helper function for the weighting associated to a simple graph -/
def weightingAux [Fintype V] (p : ℝ) (s : Finset (Sym2 V)) : ℝ :=
  p ^ s.card * (1 - p) ^ ((card V).choose 2 - s.card)

theorem weightingAux_pos [Fintype V] (hp₀ : 0 < p) (hp₁ : p < 1) : 0 < weightingAux p s :=
  mul_pos (pow_pos hp₀ _) (pow_pos (sub_pos_of_lt hp₁) _)

/-- the probability of the simple graph G appearing in the G(|V|,p) model of random graphs -/
def weighting (V : Type*) [Fintype V] (p : ℝ) (G : SimpleGraph V) [Fintype G.edgeSet] :
    ℝ :=
  weightingAux p G.edgeFinset

theorem weighting_pos [Fintype V] [Fintype G.edgeSet] (hp₀ : 0 < p) (hp₁ : p < 1) :
    0 < weighting V p G :=
  weightingAux_pos hp₀ hp₁

theorem weighting_eq [Fintype V] [Fintype G.edgeSet] [Fintype Gᶜ.edgeSet] :
    weighting V p G = p ^ G.edgeFinset.card * (1 - p) ^ Gᶜ.edgeFinset.card := by
  rw [weighting, weightingAux, card_compl_edgeFinset_eq]

theorem weighting_compl [Fintype V] [Fintype G.edgeSet] [Fintype Gᶜ.edgeSet]
    (p : ℝ) : weighting V (1 - p) (Gᶜ) = weighting V p G := by
  rw [weighting, weighting, weightingAux, weightingAux, sub_sub_self, ←
    card_edgeFinset_eq_sub_compl', ← card_compl_edgeFinset_eq, mul_comm]

theorem disjUnion_inj_left {α : Type*} {s t₁ t₂ : Finset α} {hst₁ : Disjoint s t₁}
    {hst₂ : Disjoint s t₂} : disjUnion s t₁ hst₁ = disjUnion s t₂ hst₂ → t₁ = t₂ :=
  by
  intro h
  ext i
  wlog h' : i ∈ t₁ generalizing i t₁ t₂ -- bare "wlog" generalizes too much here
  · simp only [h', false_iff]
    intro h''
    apply h'
    exact (this h.symm i h'').1 h''
  simp only [h', true_iff]
  have : i ∈ s.disjUnion t₁ hst₁ := by
    rw [mem_disjUnion]
    exact Or.inr h'
  rw [h, mem_disjUnion] at this
  exact this.resolve_left (Finset.disjoint_right.1 hst₁ h')

theorem disjUnion_inj_right {α : Type*} {s₁ s₂ t : Finset α} {hst₁ : Disjoint s₁ t}
    {hst₂ : Disjoint s₂ t} : disjUnion s₁ t hst₁ = disjUnion s₂ t hst₂ → s₁ = s₂ :=
  by
  intro h
  rw [disjUnion_comm s₁, disjUnion_comm s₂] at h
  exact disjUnion_inj_left h

attribute [local instance] Fintype.toLocallyFiniteOrder

section

variable [Fintype V] [DecidableEq V] [Fintype (SimpleGraph V)] [@DecidableRel (SimpleGraph V) (· < ·)] [@DecidableRel (SimpleGraph V) (· ≤ ·)] [∀ G : SimpleGraph V, DecidableRel G.Adj]

theorem weightingAux_sum_between (H₁ H₂ : SimpleGraph V)
    (h : H₁ ≤ H₂) :
    ∑ G in Finset.Icc H₁ H₂, weighting V p G =
      p ^ H₁.edgeFinset.card * (1 - p) ^ H₂ᶜ.edgeFinset.card :=
  by
  simp only [weighting]
  rw [← Finset.sum_image]
  swap
  · simp
  have h₁ :
    ((Icc H₁ H₂).image fun G => G.edgeFinset) =
      (H₁ᶜ ⊓ H₂).edgeFinset.powerset.image fun s => s ∪ H₁.edgeFinset :=
    by
    ext s
    simp only [mem_image, mem_powerset, mem_Icc, exists_prop, compl_sup, edgeSet_inf,
      Set.subset_toFinset, Set.subset_inter_iff, and_assoc, compl_compl]
    constructor
    · rintro ⟨G, hG₁, hG₂, rfl⟩
      refine ⟨(G \ H₁).edgeFinset, ?_, ?_, ?_⟩
      · rw [coe_edgeFinset, sdiff_eq, edgeSet_subset_edgeSet]
        exact inf_le_right
      · rw [coe_edgeFinset, edgeSet_subset_edgeSet]
        exact sdiff_le.trans hG₂
      rwa [← edgeFinset_sup', ← coe_inj, coe_edgeFinset, coe_edgeFinset, sdiff_sup_cancel]
    rintro ⟨s, hs₁, hs₂, rfl⟩
    refine ⟨fromEdgeSet s ⊔ H₁, le_sup_right, sup_le ?_ h, ?_⟩
    · exact (fromEdgeSet_mono hs₂).trans_eq (fromEdgeSet_edgeSet _)
    rw [← coe_inj, coe_union, coe_edgeFinset, coe_edgeFinset, edgeSet_sup,
      edgeSet_fromEdgeSet, sdiff_eq_left.2]
    rw [Set.disjoint_left]
    intro e he
    exact not_isDiag_of_mem_edgeSet _ (hs₁ he)
  rw [h₁, Finset.sum_image]
  swap
  · simp only [edgeFinset_inf', mem_powerset, subset_inter_iff, and_imp, compl_edgeFinset_eq,
      subset_sdiff]
    rintro G - hG₁ _ G' - hG'₁ _ h'
    rw [← disjUnion_eq_union _ _ hG₁, ← disjUnion_eq_union _ _ hG'₁] at h'
    exact disjUnion_inj_right h'
  have h₂ : ∀ x ∈ (H₁ᶜ ⊓ H₂).edgeFinset.powerset, Disjoint x H₁.edgeFinset :=
    by
    intro x
    simp (config := { contextual := true }) only [edgeFinset_inf', mem_powerset, subset_inter_iff,
      compl_edgeFinset_eq, subset_sdiff, imp_true_iff, and_imp, and_assoc]
  simp only [weightingAux]
  have : (H₁ᶜ ⊓ H₂).edgeFinset.card + H₁.edgeFinset.card = H₂.edgeFinset.card :=
    by
    rw [← card_union_of_disjoint, ← edgeFinset_sup']
    congr 1
    · rwa [← coe_inj, coe_edgeFinset, coe_edgeFinset, inf_comm, ← sdiff_eq, sdiff_sup_cancel]
    rw [← disjoint_coe, coe_edgeFinset, coe_edgeFinset, Set.disjoint_iff_inter_eq_empty, ←
      edgeSet_inf, @inf_comm _ _ (H₁ᶜ), inf_assoc, compl_inf_eq_bot, inf_bot_eq, edgeSet_bot]
  have h₃ : (H₁ᶜ ⊓ H₂).edgeFinset.card = H₂.edgeFinset.card - H₁.edgeFinset.card := by
    rw [← this, Nat.add_sub_cancel]
  have :
    p ^ H₁.edgeFinset.card * (1 - p) ^ H₂ᶜ.edgeFinset.card *
        ∑ x in (H₁ᶜ ⊓ H₂).edgeFinset.powerset,
          p ^ x.card * (1 - p) ^ ((H₁ᶜ ⊓ H₂).edgeFinset.card - x.card) =
      p ^ H₁.edgeFinset.card * (1 - p) ^ H₂ᶜ.edgeFinset.card :=
    by
    rw [Finset.sum_pow_mul_eq_add_pow p (1 - p) (H₁ᶜ ⊓ H₂).edgeFinset, add_sub_cancel,
      one_pow, mul_one]
  rw [← this, mul_comm, sum_mul]
  refine sum_congr rfl fun x hx => ?_
  rw [mul_mul_mul_comm, ← pow_add, ← pow_add, card_union_of_disjoint (h₂ x hx)]
  congr 2
  rw [h₃, card_compl_edgeFinset_eq, tsub_tsub, add_comm, add_comm (_ - _), tsub_add_tsub_cancel]
  · apply edgeFinset_card_le
  rw [add_comm, ← card_union_of_disjoint (h₂ x hx)]
  refine card_le_card ?_
  rw [mem_powerset, edgeFinset_inf, subset_inter_iff] at hx
  exact union_subset hx.2 (edgeFinset_subset_edgeFinset.2 h)

theorem sum_weighting : ∑ G, weighting V p G = 1 :=
  by
  have : Icc (⊥ : SimpleGraph V) ⊤ = Finset.univ := by
    rw [← coe_inj, coe_Icc, Set.Icc_bot_top, coe_univ]

  simp_rw [← this, weightingAux_sum_between ⊥ ⊤ bot_le, edgeFinset_bot', edgeFinset_card]
  simp only [compl_top, edgeSet_bot, Set.empty_card, card_empty, pow_zero, pow_zero, mul_one]

end

--- added explicit fintype instance for lhs
theorem card_edgeSet_map {V V' : Type*} (f : V ↪ V') (G : SimpleGraph V)
    [Fintype (edgeSet G)] [Fintype (edgeSet (G.map f))] :
    card (G.map f).edgeSet = card G.edgeSet :=
  by
  let f' := SimpleGraph.Embedding.mapEdgeSet (Embedding.map f G)
  have : Function.Bijective f' := by
    refine ⟨f'.injective, ?_⟩
    rintro ⟨x, hx⟩
    induction' x using Sym2.inductionOn with x y
    simp only [Subtype.exists]
    simp only [mem_edgeSet, map_adj] at hx
    obtain ⟨x, y, huv, rfl, rfl⟩ := hx
    exact ⟨s(x, y), huv, rfl⟩
  exact (Fintype.card_of_bijective this).symm

/-- is s a clique in G -/
def CliqueOn (G : SimpleGraph V) (s : Set V) : Prop :=
  spanningCoe (⊤ : SimpleGraph s) ≤ G

/-- is s independent in G -/
def IndepOn (G : SimpleGraph V) (t : Set V) : Prop :=
  G ≤ (spanningCoe (⊤ : SimpleGraph t))ᶜ

theorem cliqueOn_compl (s : Set V) : CliqueOn (Gᶜ) s ↔ IndepOn G s := by
  rw [CliqueOn, IndepOn, le_compl_comm]

theorem indepOn_iff {t : Set V} : IndepOn G t ↔ Disjoint G (spanningCoe (⊤ : SimpleGraph t)) := by
  rw [IndepOn, le_compl_iff_disjoint_right]

instance decidableAdjMap [Fintype V] {V' : Type*} [DecidableEq V'] {G : SimpleGraph V}
    [DecidableRel G.Adj] {f : V ↪ V'} : DecidableRel (G.map f).Adj := fun _ _ =>
  decidable_of_iff' _ (G.map_adj f _ _)

theorem card_edgeSet_spanningCoe_top [Fintype V] [DecidableEq V] (s : Finset V)
    [Fintype (⊤ : SimpleGraph s).spanningCoe.edgeSet] :
    Fintype.card (spanningCoe (⊤ : SimpleGraph s)).edgeSet = s.card.choose 2 :=
  by
  rw [@card_edgeSet_map s, card_top_edgeSet] -- needed to pass in s explicitly
  change (Fintype.card s).choose 2 = _
  rw [Fintype.card_coe]

instance decidableLe [Fintype V] {H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj] :
    Decidable (G ≤ H) :=
  Fintype.decidableForallFintype

instance decidablePredCliqueOn [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    DecidablePred fun s : Finset V => CliqueOn G s := fun _ => SimpleGraph.decidableLe

instance decidablePredIndepOn [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    DecidablePred fun s : Finset V => IndepOn G s := fun _ => SimpleGraph.decidableLe

theorem Le.def {V : Type*} {G H : SimpleGraph V} : G ≤ H ↔ ∀ ⦃x y : V⦄, G.Adj x y → H.Adj x y :=
  Iff.rfl

theorem Fin.fin_two_eq_zero_iff_ne_one {x : Fin 2} : x = 0 ↔ x ≠ 1 :=
  by
  revert x
  rw [Fin.forall_fin_two]
  simp

theorem cliqueOn_monochromaticOf {K : Type*} (C : TopEdgeLabelling V K) (k : K) (m : Set V) :
    CliqueOn (C.labelGraph k) m ↔ C.MonochromaticOf m k :=
  by
  simp only [CliqueOn, TopEdgeLabelling.MonochromaticOf, Le.def, map_adj, SetCoe.exists,
    TopEdgeLabelling.labelGraph_adj, Function.Embedding.coe_subtype, Subtype.coe_mk, top_adj,
    Ne.eq_def, Subtype.mk_eq_mk, forall_exists_index, and_imp]
  constructor
  · intro h x hx y hy h'
    obtain ⟨_, z⟩ := h x hx y hy h' rfl rfl
    exact z
  · rintro h x y a ha b hb hab rfl rfl
    exact ⟨hab, h ha hb _⟩

theorem labelGraph_fin_two_compl (C : TopEdgeLabelling V (Fin 2)) :
    (C.labelGraph 1)ᶜ = C.labelGraph 0 := by
  classical rw [← labelGraph_toEdgeLabelling C, toEdgeLabelling_labelGraph,
    toEdgeLabelling_labelGraph_compl]

theorem indepOn_monochromaticOf (C : TopEdgeLabelling V (Fin 2)) (m : Set V) :
    IndepOn (C.labelGraph 1) m ↔ C.MonochromaticOf m 0 := by
  rw [← cliqueOn_compl, labelGraph_fin_two_compl, cliqueOn_monochromaticOf]

/-- the number of cliques of size k in the graph G -/
def numberOfCliques [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    ℕ :=
  ((univ.powersetCard k).filter fun s : Finset V => G.CliqueOn s).card

/-- the number of independent sets of size l in the graph G -/
def numberOfIndeps [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (l : ℕ) :
    ℕ :=
  ((univ.powersetCard l).filter fun s : Finset V => G.IndepOn s).card

theorem numberOfCliques_compl [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [DecidableRel Gᶜ.Adj]
    {k : ℕ} : numberOfCliques (Gᶜ) k = numberOfIndeps G k :=
  by
  rw [numberOfCliques, numberOfIndeps]
  simp only [cliqueOn_compl]

/-- the number of cliques of size k + the number of independent sets of size l -/
def numberOfThings [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (k l : ℕ) :
    ℕ :=
  G.numberOfCliques k + G.numberOfIndeps l

section

variable [Fintype V] [DecidableEq V] [Fintype (SimpleGraph V)] [@DecidableRel (SimpleGraph V) (· < ·)] [@DecidableRel (SimpleGraph V) (· ≤ ·)] [∀ G : SimpleGraph V, DecidableRel G.Adj]

theorem weighted_number_cliques {k : ℕ} :
    ∑ G, weighting V p G * G.numberOfCliques k = (card V).choose k * p ^ k.choose 2 :=
  by
  simp_rw [numberOfCliques, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, sum_filter, mul_sum,
    @sum_comm _ _ (SimpleGraph V), mul_boole, ← sum_filter]
  rw [← nsmul_eq_mul, ← card_univ, ← card_powersetCard, ← sum_const]
  refine sum_congr rfl ?_
  intro x hx
  have :
    (univ.filter fun a : SimpleGraph V => a.CliqueOn x) =
      Icc (spanningCoe (⊤ : SimpleGraph x)) ⊤ :=
    by
    ext G
    simp only [mem_filter, mem_univ, true_and, mem_Icc, le_top, and_true, CliqueOn]
    rfl
  rw [this]
  have : ∑ G : SimpleGraph V in _, weighting V p G = _ :=
    weightingAux_sum_between (spanningCoe (⊤ : SimpleGraph x)) ⊤ le_top
  rw [edgeFinset_card, edgeFinset_card] at this
  simp only [compl_top, edgeSet_bot, Set.empty_card', pow_zero, mul_one] at this
  suffices h : Fintype.card ((spanningCoe (⊤ : SimpleGraph x)).edgeSet) = k.choose 2 by simp only [h, this]
  convert (card_edgeSet_spanningCoe_top x).trans _
  rw [mem_powersetCard] at hx
  simp only [hx]

theorem weighted_number_indeps {k : ℕ} :
    ∑ G, weighting V p G * G.numberOfIndeps k = (card V).choose k * (1 - p) ^ k.choose 2 :=
  by
  simp only [← numberOfCliques_compl]
  simp only [← weighting_compl p]
  rw [← weighted_number_cliques]
  refine sum_bij' (fun G _ => Gᶜ) (fun G _ => Gᶜ) (fun _ _ => mem_univ _) (fun _ _ => mem_univ _) ?_ ?_ ?_
  · intro a ha
    simp_rw [compl_compl]
  · intro a ha
    simp_rw [compl_compl]
  · intro a ha
    refine congr_arg₂ (· * ·) ?_ ?_
    · congr! 1
    · refine congr_arg _ ?_
      change Finset.card _ = Finset.card _
      refine congr_arg _ ?_
      ext i
      refine mem_filter.trans ?_
      simp_rw [mem_filter]

theorem weighted_number_things {k l : ℕ} :
    ∑ G, weighting V p G * G.numberOfThings k l =
      (card V).choose k * p ^ k.choose 2 + (card V).choose l * (1 - p) ^ l.choose 2 :=
  by
  simp only [numberOfThings, Nat.cast_add, mul_add, sum_add_distrib, weighted_number_cliques,
    weighted_number_indeps]

end

theorem basic_bound [Fintype V] {k l : ℕ} {p : ℝ} (hp : 0 < p) (hp' : p < 1)
    (hV : ((card V).choose k : ℝ) * p ^ k.choose 2 + (card V).choose l * (1 - p) ^ l.choose 2 < 1) :
    ∃ G : SimpleGraph V,
      (∀ X : Finset V, X.card = k → ¬G.CliqueOn X) ∧ ∀ X : Finset V, X.card = l → ¬G.IndepOn X :=
  by
  classical
  by_contra!
  refine hV.not_le ?_
  rw [← weighted_number_things, ← @sum_weighting V p _]
  refine sum_le_sum ?_
  intro i _
  refine le_mul_of_one_le_right ?_ ?_
  swap
  · rw [Nat.one_le_cast, numberOfThings, Nat.succ_le_iff, add_pos_iff, numberOfCliques,
      numberOfIndeps, card_pos, card_pos, filter_nonempty_iff, filter_nonempty_iff]
    simp only [exists_prop, mem_powersetCard_univ, or_iff_not_imp_left, not_exists, not_and]
    exact this _
  letI := Classical.decRel i.Adj
  exact (weighting_pos hp hp').le

theorem basic_ramsey_bound {k l n : ℕ} {p : ℝ} (hp : 0 < p) (hp' : p < 1)
    (hV : (n.choose k : ℝ) * p ^ k.choose 2 + n.choose l * (1 - p) ^ l.choose 2 < 1) :
    n < ramseyNumber ![k, l] := by
  rw [← Fintype.card_fin n]
  rw [← Fintype.card_fin n] at hV
  rw [← not_le, ramseyNumber_pair_swap, ramseyNumber_le_iff, isRamseyValid_iff_eq]
  intro h
  obtain ⟨G, hG₁, hG₂⟩ := basic_bound hp hp' hV
  letI := Classical.decRel G.Adj
  let C := G.toEdgeLabelling
  obtain ⟨m, hm⟩ := h C
  rw [Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, ←
    indepOn_monochromaticOf, ← cliqueOn_monochromaticOf, toEdgeLabelling_labelGraph] at hm
  rcases hm with (hm | hm)
  · exact hG₂ m hm.2.symm hm.1
  · exact hG₁ m hm.2.symm hm.1

open Real

theorem sq_div_four_le_choose_two {k : ℕ} (hk : 2 ≤ k) : (k ^ 2 / 4 : ℝ) ≤ k.choose 2 :=
  by
  rw [Nat.cast_choose_two, sq, mul_div_assoc, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  have : (2 : ℝ) ≤ k := by exact_mod_cast hk
  linarith

-- meant to be used when p *very* small
theorem basic_off_diagonal_ramsey_bound {k l n : ℕ} {p : ℝ} (hp : 0 < p) (hp' : p < 1) (hk : 2 ≤ k)
    (hl : 2 ≤ l) (hV : (n : ℝ) ^ k * p ^ (k ^ 2 / 4 : ℝ) + n ^ l * exp (-p * l ^ 2 / 4) < 1) :
    n < ramseyNumber ![k, l] :=
  by
  refine basic_ramsey_bound hp hp' (hV.trans_le' (add_le_add ?_ ?_))
  · refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
    · refine (Nat.choose_le_pow_div _ _).trans ?_
      refine div_le_self (by positivity) ?_
      rw [Nat.one_le_cast, Nat.succ_le_iff]
      exact Nat.factorial_pos _
    · rw [← rpow_natCast]
      exact rpow_le_rpow_of_exponent_ge hp hp'.le (sq_div_four_le_choose_two hk)
  · refine mul_le_mul ?_ ?_ ?_ (by positivity)
    · refine (Nat.choose_le_pow_div _ _).trans ?_
      refine div_le_self (by positivity) ?_
      rw [Nat.one_le_cast, Nat.succ_le_iff]
      exact Nat.factorial_pos _
    · refine (pow_le_pow_left (by linarith) (one_sub_le_exp_neg p) _).trans ?_
      rw [← rpow_natCast, ← exp_one_rpow, ← rpow_mul (exp_pos _).le, exp_one_rpow, exp_le_exp,
        mul_div_assoc]
      refine mul_le_mul_of_nonpos_left ?_ (by simpa using hp.le)
      exact sq_div_four_le_choose_two hl
    exact pow_nonneg (by linarith) _

theorem basic_diagonalRamsey_bound {k n : ℕ}
    (hV : (n.choose k : ℝ) * 2 ^ (1 - k.choose 2 : ℝ) < 1) : n < diagonalRamsey k :=
  by
  refine basic_ramsey_bound (show 0 < (2 : ℝ)⁻¹ by norm_num) (by norm_num) ?_
  norm_num1
  rwa [one_div, ← two_mul, ← Real.rpow_natCast, mul_left_comm, Real.inv_rpow, ← Real.rpow_neg,
      mul_comm (2 : ℝ), ← Real.rpow_add_one, add_comm, ← sub_eq_add_neg] <;>
    norm_num1

theorem diagonalRamsey_bound_refined_aux {n k : ℕ} (hk : k ≠ 0)
    (hn : (n : ℝ) ≤ (exp 1 * sqrt 2)⁻¹ * 2 ^ (-1 / k : ℝ) * k * sqrt 2 ^ k) :
    n < diagonalRamsey k := by
  refine basic_diagonalRamsey_bound ?_
  have : (n : ℝ) ^ k ≤ 2 ^ (-1 : ℝ) * (sqrt 2 ^ (k - 1 : ℝ)) ^ k * (k / exp 1) ^ k :=
    by
    refine (pow_le_pow_left (Nat.cast_nonneg _) hn _).trans_eq ?_
    rw [mul_inv, mul_right_comm _ (sqrt 2)⁻¹, mul_right_comm _ (sqrt 2)⁻¹, mul_assoc, ←
      rpow_neg_one (sqrt 2), ← rpow_natCast (sqrt 2), ← rpow_add, neg_add_eq_sub, mul_pow,
      mul_comm (exp 1)⁻¹, mul_right_comm, mul_assoc, ← div_eq_mul_inv, mul_pow, ← rpow_natCast, ←
      rpow_mul, div_mul_cancel₀, mul_right_comm]
    · positivity
    · positivity
    · positivity
  rw [← div_le_iff₀ _, ← div_pow, div_div_eq_mul_div, mul_comm] at this
  swap
  · positivity
  rcases eq_or_ne n 0 with (rfl | hn')
  · cases k
    · simp at hk
    rw [Nat.choose_zero_succ, Nat.cast_zero, MulZeroClass.zero_mul]
    norm_num1
  refine (mul_lt_mul_of_pos_right (choose_upper_bound_of_pos hn' hk) (by positivity)).trans_le ?_
  refine (mul_le_mul_of_nonneg_right this (by positivity)).trans_eq ?_
  rw [← rpow_div_two_eq_sqrt, ← rpow_natCast, ← rpow_mul, ← rpow_add, ← rpow_add,
    Nat.cast_choose_two]
  · ring_nf
  · norm_num1
  · norm_num1
  · norm_num1
  · norm_num1

theorem diagonalRamsey_bound_refined {k : ℕ} (hk : k ≠ 0) :
    (exp 1 * sqrt 2)⁻¹ * 2 ^ (-1 / k : ℝ) * k * sqrt 2 ^ k < diagonalRamsey k :=
  by
  have hk' : 0 ≤ (exp 1 * sqrt 2)⁻¹ * 2 ^ (-1 / k : ℝ) * k * sqrt 2 ^ k := by positivity
  rw [← Nat.floor_lt hk']
  exact diagonalRamsey_bound_refined_aux hk (Nat.floor_le hk')

theorem diagonalRamsey_bound_refined_again {k : ℕ} (hk : k ≠ 0) :
    (exp 1 * sqrt 2)⁻¹ * (1 - log 2 / k) * k * sqrt 2 ^ k < diagonalRamsey k :=
  by
  refine (diagonalRamsey_bound_refined hk).trans_le' ?_
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (one_sub_le_exp_neg _).trans_eq ?_
  rw [rpow_def_of_pos, neg_div, mul_neg, mul_one_div]
  norm_num1

theorem e_times_sqrt_two_plus_log_two_gt_four : 4 < exp 1 * sqrt 2 + log 2 := by
  have : 1.4 < sqrt 2 := by rw [lt_sqrt] <;> norm_num
  nlinarith [log_two_gt_d9, exp_one_gt_d9]

theorem e_times_sqrt_two_plus_log_two_lt_five : exp 1 * sqrt 2 + log 2 < 5 :=
  by
  have : sqrt 2 < 1.5 := by rw [sqrt_lt] <;> norm_num
  nlinarith [log_two_lt_d9, exp_one_lt_d9, exp_one_gt_d9]

theorem diagonalRamsey_bound_simpler_aux {k : ℕ} (hk' : exp 1 * sqrt 2 + log 2 ≤ k) :
    sqrt 2 ^ k < diagonalRamsey k :=
  by
  have : k ≠ 0 := by
    have := e_times_sqrt_two_plus_log_two_gt_four.trans_le hk'
    norm_cast at this
    rw [← pos_iff_ne_zero]
    exact this.trans_le' (by norm_num)
  refine (diagonalRamsey_bound_refined_again this).trans_le' ?_
  refine le_mul_of_one_le_left (by positivity) ?_
  rwa [mul_assoc, one_sub_mul, div_mul_cancel₀, inv_mul_eq_div, one_le_div, le_sub_iff_add_le]
  · positivity
  · positivity

theorem diagonalRamsey_lower_bound_simpler {k : ℕ} (hk : 2 ≤ k) : sqrt 2 ^ k ≤ diagonalRamsey k := by
  rcases le_total (exp 1 * sqrt 2 + log 2) k with (h | h)
  · exact (diagonalRamsey_bound_simpler_aux h).le
  replace h := h.trans_lt e_times_sqrt_two_plus_log_two_lt_five
  norm_cast at h
  interval_cases k
  · rw [sq_sqrt, diagonalRamsey_two, Nat.cast_two]; exact zero_le_two
  · rw [diagonalRamsey_three]
    refine (abs_le_of_sq_le_sq' ?_ (by norm_num)).2
    rw [← pow_mul, pow_mul', sq_sqrt] <;> norm_num
  rw [pow_mul' _ 2 2, sq_sqrt, diagonalRamsey_four] <;> norm_num

/-- An Erdos-Szekeres upper bound on Ramsey numbers, with the error term made precise -/
theorem diagonalRamsey_upper_bound_refined {k : ℕ} :
    (diagonalRamsey k : ℝ) ≤ 4 ^ (k - 1) / sqrt (Real.pi * (k - 3 / 4)) :=
  by
  rcases k.eq_zero_or_pos with (rfl | hk)
  · rw [diagonalRamsey_zero, Nat.cast_zero, Nat.zero_sub, pow_zero, one_div, inv_nonneg]
    exact sqrt_nonneg _
  refine (Nat.cast_le.2 (diagonalRamsey_le_centralBinom k)).trans ?_
  refine (centralBinomialUpper_bound (k - 1)).trans ?_
  have : (1 : ℝ) ≤ k := by rwa [Nat.one_le_cast, Nat.succ_le_iff]
  refine div_le_div_of_nonneg_left (by positivity) (sqrt_pos_of_pos (mul_pos pi_pos ?_)) ?_
  · linarith only [this]
  refine sqrt_le_sqrt (mul_le_mul_of_nonneg_left ?_ pi_pos.le)
  rw [Nat.cast_sub, Nat.cast_one]
  · linarith only
  rwa [Nat.one_le_cast] at this

theorem diagonalRamsey_upper_bound_simpler {k : ℕ} : (diagonalRamsey k : ℝ) ≤ 4 ^ k / sqrt k :=
  by
  rcases k.eq_zero_or_pos with (rfl | hk)
  · rw [diagonalRamsey_zero, Nat.cast_zero, pow_zero, sqrt_zero, div_zero]
  refine' diagonalRamsey_upper_bound_refined.trans _
  rw [pow_sub₀ _ _ hk, ← div_eq_mul_inv, div_div]
  swap; · positivity
  refine' div_le_div_of_nonneg_left (by positivity) (by positivity) _
  have : (4 : ℝ) ^ 1 = sqrt 16 :=
    by
    have : (16 : ℝ) = 4 ^ 2 := by norm_num
    rw [pow_one, this, sqrt_sq]
    norm_num
  rw [this, ← sqrt_mul]
  swap; · norm_num1
  refine' sqrt_le_sqrt _
  suffices 12 * Real.pi ≤ k * (16 * Real.pi - 1) by linarith
  have : 49 ≤ 16 * Real.pi - 1 := by linarith only [pi_gt_d6]
  refine' (mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)).trans' _
  have : 12 * Real.pi ≤ 38 := by linarith only [pi_lt_d2]
  have : (1 : ℝ) ≤ k := Nat.one_le_cast.2 hk
  linarith

section

open Filter

/--
A lower bound on diagonal Ramsey numbers, as given on wikipedia. This is within a factor 2 of the
best known lower bound.
It says R(k, k) ≥ (1 + o(1)) * k / (e √2) * 2 ^ (k / 2)
`diagonalRamsey_bound_refined_again` makes the o(1) term more precise, and
`diagonalRamsey_lower_bound_simpler` simplifies the lower order terms for convenience.
-/
theorem little_o_lower_ramsey_bound :
    ∃ f : ℕ → ℝ,
      f =o[atTop] (fun _ => 1 : _ → ℝ) ∧
        ∀ k, (1 + f k) * k / (sqrt 2 * exp 1) * sqrt 2 ^ k ≤ diagonalRamsey k :=
  by
  refine ⟨fun k => -log 2 / k, ?_, fun k => ?_⟩
  · rw [Asymptotics.isLittleO_one_iff]
    exact tendsto_const_div_atTop_nhds_zero_nat _
  rcases eq_or_ne k 0 with (rfl | hk)
  · simp
  refine (diagonalRamsey_bound_refined_again hk).le.trans_eq' ?_
  dsimp only
  rw [neg_div, ← sub_eq_add_neg, div_eq_mul_inv, mul_comm (sqrt 2), mul_comm (_ * _) _⁻¹, ←
    mul_assoc]

end

end SimpleGraph
