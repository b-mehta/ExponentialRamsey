/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Sym.Card

#align_import prereq.mathlib.combinatorics.simple_graph.basic

/-!
# Stuff for combinatorics.simple_graph.basic
-/


namespace SimpleGraph

variable {V V' : Type _} {G : SimpleGraph V} {K K' : Type _}

open Fintype (card)

open Finset

instance [Subsingleton V] : IsEmpty (edgeSetEmbedding G) :=
  by
  constructor
  rintro ⟨i, hi⟩
  induction' i using Sym2.inductionOn with i j
  simp only [mem_edge_set] at hi
  cases hi.ne (Subsingleton.elim _ _)

/-- The edge set of the complete graph on V is in bijection with the off-diagonal elements of sym2 V
TODO: maybe this should be an equality of sets?
and then turn it into a bijection of types
-/
def topEdgeSetEquiv : (⊤ : SimpleGraph V).edgeSetEmbedding ≃ { a : Sym2 V // ¬a.IsDiag } :=
  Equiv.subtypeEquivRight fun i => Sym2.inductionOn i fun x y => Iff.rfl

theorem card_top_edgeSetEmbedding [DecidableEq V] [Fintype V] :
    card (⊤ : SimpleGraph V).edgeSetEmbedding = (card V).choose 2 := by
  rw [Fintype.card_congr top_edge_set_equiv, Sym2.card_subtype_not_diag]

theorem edgeSetEmbedding_eq_empty_iff {G : SimpleGraph V} : G.edgeSetEmbedding = ∅ ↔ G = ⊥ := by
  rw [← edge_set_bot, edge_set_inj]

theorem disjoint_edge_set {G H : SimpleGraph V} :
    Disjoint G.edgeSetEmbedding H.edgeSetEmbedding ↔ Disjoint G H := by
  rw [Set.disjoint_iff_inter_eq_empty, disjoint_iff, ← edge_set_inf, edge_set_eq_empty_iff]

theorem disjoint_left {G H : SimpleGraph V} : Disjoint G H ↔ ∀ x y, G.Adj x y → ¬H.Adj x y := by
  simp only [← disjoint_edge_set, Set.disjoint_left, Sym2.forall, mem_edge_set]

@[simp]
theorem adj_sup_iff {ι V : Type _} {s : Finset ι} {f : ι → SimpleGraph V} {x y : V} :
    (s.sup f).Adj x y ↔ ∃ i ∈ s, (f i).Adj x y :=
  by
  induction' s using Finset.cons_induction_on with a s has ih
  · simp
  · simp [or_and_right, exists_or, ih]

theorem top_hom_injective (f : (⊤ : SimpleGraph V') →g G) : Function.Injective f := fun x y h =>
  by_contra fun z => (f.map_rel z).Ne h

/-- graph embeddings from a complete graph are in bijection with graph homomorphisms from it -/
def topHomGraphEquiv : (⊤ : SimpleGraph V') ↪g G ≃ (⊤ : SimpleGraph V') →g G
    where
  toFun f := f
  invFun f := ⟨⟨f, top_hom_injective _⟩, fun x y => ⟨fun h => ne_of_apply_ne _ h.Ne, f.map_rel⟩⟩
  left_inv f := RelEmbedding.ext fun _ => rfl
  right_inv f := RelHom.ext fun _ => rfl

theorem neighborSet_bot {x : V} : (⊥ : SimpleGraph V).neighborSet x = ∅ := by ext y; simp

theorem neighborSet_top {x : V} : (⊤ : SimpleGraph V).neighborSet x = {x}ᶜ := by ext y;
  rw [mem_neighbor_set, top_adj, Set.mem_compl_singleton_iff, ne_comm]

theorem neighborSet_sup {G H : SimpleGraph V} {x : V} :
    (G ⊔ H).neighborSet x = G.neighborSet x ∪ H.neighborSet x := by ext y; simp

theorem neighborSet_inf {G H : SimpleGraph V} {x : V} :
    (G ⊓ H).neighborSet x = G.neighborSet x ∩ H.neighborSet x := by ext y;
  simp only [mem_neighbor_set, inf_adj, Set.mem_inter_iff]

theorem neighborSet_iSup {ι : Type _} {s : ι → SimpleGraph V} {x : V} :
    (⨆ i, s i).neighborSet x = ⋃ i, (s i).neighborSet x := by ext y; simp

theorem neighborSet_iInf {ι : Type _} [Nonempty ι] {s : ι → SimpleGraph V} {x : V} :
    (⨅ i, s i).neighborSet x = ⋂ i, (s i).neighborSet x :=
  by
  ext y
  simp only [mem_neighbor_set, infi_adj, Ne.def, Set.iInf_eq_iInter, Set.mem_iInter,
    and_iff_left_iff_imp]
  intro h
  inhabit ι
  exact (h default).Ne

theorem neighborSet_disjoint {G H : SimpleGraph V} {x : V} (h : Disjoint G H) :
    Disjoint (G.neighborSet x) (H.neighborSet x) := by
  rw [Set.disjoint_iff_inter_eq_empty, ← neighbor_set_inf, h.eq_bot, neighbor_set_bot]

section

instance {V : Type _} {x : V} : IsEmpty ((⊥ : SimpleGraph V).neighborSet x) :=
  Subtype.isEmpty_false

theorem neighborFinset_bot {x : V} : (⊥ : SimpleGraph V).neighborFinset x = ∅ := by ext y; simp

theorem neighborFinset_top [Fintype V] [DecidableEq V] {x : V} :
    (⊤ : SimpleGraph V).neighborFinset x = {x}ᶜ := by ext y;
  rw [mem_neighbor_finset, top_adj, Finset.mem_compl, mem_singleton, ne_comm]

theorem neighborFinset_sup [DecidableEq V] {G H : SimpleGraph V} {x : V}
    [Fintype ((G ⊔ H).neighborSet x)] [Fintype (G.neighborSet x)] [Fintype (H.neighborSet x)] :
    (G ⊔ H).neighborFinset x = G.neighborFinset x ∪ H.neighborFinset x := by ext y; simp

theorem neighborFinset_inf [DecidableEq V] {G H : SimpleGraph V} {x : V}
    [Fintype ((G ⊓ H).neighborSet x)] [Fintype (G.neighborSet x)] [Fintype (H.neighborSet x)] :
    (G ⊓ H).neighborFinset x = G.neighborFinset x ∩ H.neighborFinset x := by ext y; simp

instance Finset.decidableRelSup {ι V : Type _} {s : Finset ι} {f : ι → SimpleGraph V}
    [∀ i, DecidableRel (f i).Adj] : DecidableRel (s.sup f).Adj := fun x y =>
  decidable_of_iff' _ adj_sup_iff

theorem neighborFinset_supr [DecidableEq V] {ι : Type _} {s : Finset ι} {f : ι → SimpleGraph V}
    {x : V} [∀ i, Fintype ((f i).neighborSet x)] [Fintype ((s.sup f).neighborSet x)] :
    (s.sup f).neighborFinset x = s.biUnion fun i => (f i).neighborFinset x := by ext y; simp

@[simp]
theorem coe_neighborFinset {G : SimpleGraph V} {x : V} [Fintype (G.neighborSet x)] :
    (G.neighborFinset x : Set V) = G.neighborSet x := by rw [neighbor_finset_def, Set.coe_toFinset]

theorem neighborFinset_disjoint {G H : SimpleGraph V} {x : V} [Fintype (G.neighborSet x)]
    [Fintype (H.neighborSet x)] (h : Disjoint G H) :
    Disjoint (G.neighborFinset x) (H.neighborFinset x) := by
  rw [← disjoint_coe, coe_neighbor_finset, coe_neighbor_finset]; exact neighbor_set_disjoint h

end

theorem degree_eq_zero_iff {v : V} [Fintype (G.neighborSet v)] : G.degree v = 0 ↔ ∀ w, ¬G.Adj v w :=
  by rw [← not_exists, ← degree_pos_iff_exists_adj, not_lt, le_zero_iff]

theorem comap_comap {V W X : Type _} {G : SimpleGraph V} {f : W → V} {g : X → W} :
    (G.comap f).comap g = G.comap (f ∘ g) :=
  rfl

end SimpleGraph

