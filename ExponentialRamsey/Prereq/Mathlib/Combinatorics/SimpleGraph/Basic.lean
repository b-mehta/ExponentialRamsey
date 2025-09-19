/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Sym.Card

/-!
# Stuff for combinatorics.simple_graph.basic
-/


namespace SimpleGraph

variable {V V' : Type*} {G : SimpleGraph V} {K K' : Type*}

open Fintype (card)

open Finset

instance [Subsingleton V] : IsEmpty (edgeSet G) := by
  constructor
  rintro ⟨i, hi⟩
  induction i using Sym2.inductionOn
  simp only [mem_edgeSet] at hi
  cases hi.ne (Subsingleton.elim _ _)

/-- The edge set of the complete graph on V is in bijection with the off-diagonal elements of sym2 V
TODO: maybe this should be an equality of sets?
and then turn it into a bijection of types
-/
def topEdgeSetEquiv : (⊤ : SimpleGraph V).edgeSet ≃ { a : Sym2 V // ¬a.IsDiag } :=
  Equiv.subtypeEquivRight fun i => Sym2.inductionOn i fun _ _ => Iff.rfl

theorem card_top_edgeSet [DecidableEq V] [Fintype V] :
    card (⊤ : SimpleGraph V).edgeSet = (card V).choose 2 := by
  rw [Fintype.card_congr topEdgeSetEquiv, Sym2.card_subtype_not_diag]

theorem edgeSet_eq_empty_iff {G : SimpleGraph V} : G.edgeSet = ∅ ↔ G = ⊥ := by
  rw [← edgeSet_bot, edgeSet_inj]

-- now in mathlib
-- theorem disjoint_edgeSet {G H : SimpleGraph V} :
--     Disjoint G.edgeSet H.edgeSet ↔ Disjoint G H := by
--   rw [Set.disjoint_iff_inter_eq_empty, disjoint_iff, ← edgeSet_inf, edgeSet_eq_empty_iff]

theorem disjoint_left {G H : SimpleGraph V} : Disjoint G H ↔ ∀ x y, G.Adj x y → ¬H.Adj x y := by
  simp only [← disjoint_edgeSet, Set.disjoint_left, Sym2.forall, mem_edgeSet]

@[simp]
theorem adj_sup_iff {ι V : Type*} {s : Finset ι} {f : ι → SimpleGraph V} {x y : V} :
    (s.sup f).Adj x y ↔ ∃ i ∈ s, (f i).Adj x y :=
  Finset.cons_induction_on s (by simp) (by simp +contextual [or_and_right, exists_or])

theorem top_hom_injective (f : (⊤ : SimpleGraph V') →g G) : Function.Injective f :=
  fun _ _ h => by_contra fun z => (f.map_rel z).ne h

/-- graph embeddings from a complete graph are in bijection with graph homomorphisms from it -/
def topHomGraphEquiv : (⊤ : SimpleGraph V') ↪g G ≃ (⊤ : SimpleGraph V') →g G
    where
  toFun f := f
  invFun f := ⟨⟨f, top_hom_injective _⟩, ⟨fun h => ne_of_apply_ne _ h.ne, f.map_rel⟩⟩
  left_inv _ := RelEmbedding.ext fun _ => rfl
  right_inv _ := RelHom.ext fun _ => rfl

theorem neighborSet_bot {x : V} : (⊥ : SimpleGraph V).neighborSet x = ∅ := by ext y; simp

theorem neighborSet_top {x : V} : (⊤ : SimpleGraph V).neighborSet x = {x}ᶜ := by
  ext y
  rw [mem_neighborSet, top_adj, Set.mem_compl_singleton_iff, ne_comm]

theorem neighborSet_sup {G H : SimpleGraph V} {x : V} :
    (G ⊔ H).neighborSet x = G.neighborSet x ∪ H.neighborSet x := by ext y; simp

theorem neighborSet_inf {G H : SimpleGraph V} {x : V} :
    (G ⊓ H).neighborSet x = G.neighborSet x ∩ H.neighborSet x := by
  ext y;
  simp only [mem_neighborSet, inf_adj, Set.mem_inter_iff]

theorem neighborSet_iSup {ι : Type*} {s : ι → SimpleGraph V} {x : V} :
    (⨆ i, s i).neighborSet x = ⋃ i, (s i).neighborSet x := by ext y; simp

theorem neighborSet_iInf {ι : Type*} [Nonempty ι] {s : ι → SimpleGraph V} {x : V} :
    (⨅ i, s i).neighborSet x = ⋂ i, (s i).neighborSet x :=
  by
  ext y
  simp only [mem_neighborSet, iInf_adj, Ne.eq_def, Set.mem_iInter, and_iff_left_iff_imp]
  intro h
  inhabit ι
  exact (h default).ne

theorem neighborSet_disjoint {G H : SimpleGraph V} {x : V} (h : Disjoint G H) :
    Disjoint (G.neighborSet x) (H.neighborSet x) := by
  rw [Set.disjoint_iff_inter_eq_empty, ← neighborSet_inf, h.eq_bot, neighborSet_bot]

section

instance {V : Type*} {x : V} : IsEmpty ((⊥ : SimpleGraph V).neighborSet x) :=
  Subtype.isEmpty_false

theorem neighborFinset_bot {x : V} [Fintype (neighborSet ⊥ x)] :
  (⊥ : SimpleGraph V).neighborFinset x = ∅ := by ext y; simp

theorem neighborFinset_top [Fintype V] [DecidableEq V] {x : V} :
    (⊤ : SimpleGraph V).neighborFinset x = {x}ᶜ := by
  ext y
  rw [mem_neighborFinset, top_adj, Finset.mem_compl, mem_singleton, ne_comm]

theorem neighborFinset_sup [DecidableEq V] {G H : SimpleGraph V} {x : V}
    [Fintype ((G ⊔ H).neighborSet x)] [Fintype (G.neighborSet x)] [Fintype (H.neighborSet x)] :
    (G ⊔ H).neighborFinset x = G.neighborFinset x ∪ H.neighborFinset x := by ext y; simp

theorem neighborFinset_inf [DecidableEq V] {G H : SimpleGraph V} {x : V}
    [Fintype ((G ⊓ H).neighborSet x)] [Fintype (G.neighborSet x)] [Fintype (H.neighborSet x)] :
    (G ⊓ H).neighborFinset x = G.neighborFinset x ∩ H.neighborFinset x := by ext y; simp

instance Finset.decidableRelSup {ι V : Type*} {s : Finset ι} {f : ι → SimpleGraph V}
    [∀ i, DecidableRel (f i).Adj] : DecidableRel (s.sup f).Adj := fun _ _ =>
  decidable_of_iff' _ adj_sup_iff

theorem neighborFinset_supr [DecidableEq V] {ι : Type*} {s : Finset ι} {f : ι → SimpleGraph V}
    {x : V} [∀ i, Fintype ((f i).neighborSet x)] [Fintype ((s.sup f).neighborSet x)] :
    (s.sup f).neighborFinset x = s.biUnion fun i => (f i).neighborFinset x := by ext y; simp

@[simp]
theorem coe_neighborFinset {G : SimpleGraph V} {x : V} [Fintype (G.neighborSet x)] :
    (G.neighborFinset x : Set V) = G.neighborSet x := by rw [neighborFinset_def, Set.coe_toFinset]

theorem neighborFinset_disjoint {G H : SimpleGraph V} {x : V} [Fintype (G.neighborSet x)]
    [Fintype (H.neighborSet x)] (h : Disjoint G H) :
    Disjoint (G.neighborFinset x) (H.neighborFinset x) := by
  rw [← disjoint_coe, coe_neighborFinset, coe_neighborFinset]; exact neighborSet_disjoint h

end

theorem degree_eq_zero_iff {v : V} [Fintype (G.neighborSet v)] : G.degree v = 0 ↔ ∀ w, ¬G.Adj v w :=
  by rw [← not_exists, ← degree_pos_iff_exists_adj, not_lt, Nat.le_zero]

-- already in mathlib now
-- theorem comap_comap {V W X : Type*} {G : SimpleGraph V} {f : W → V} {g : X → W} :
--     (G.comap f).comap g = G.comap (f ∘ g) :=
--   rfl

end SimpleGraph
