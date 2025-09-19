/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.CharP.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.DFinsupp.WellFounded
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finset.Pairwise
import Mathlib.Data.Sym.Card
import Mathlib.Tactic.FinCases
import ExponentialRamsey.Prereq.RamseyPrereq

/-!
# Ramsey numbers

Define edge labellings, monochromatic subsets and ramsey numbers, and prove basic properties of
these.
-/

open Finset
open Fintype (card)

namespace SimpleGraph

variable {V V' : Type*} {G : SimpleGraph V} {G' : SimpleGraph V'} {K K' : Type*}


/-- An edge labelling of a simple graph `G` with labels in type `K`. Sometimes this is called an
edge-colouring, but we reserve that terminology for labellings where incident edges cannot share a
label.
-/
def EdgeLabelling (G : SimpleGraph V) (K : Type*) :=
  G.edgeSet → K

instance [DecidableEq V] [Fintype G.edgeSet] [Fintype K] : Fintype (EdgeLabelling G K) :=
  Pi.instFintype

instance [Nonempty K] : Nonempty (EdgeLabelling G K) :=
  Pi.instNonempty

instance [Inhabited K] : Inhabited (EdgeLabelling G K) :=
  Pi.instInhabited

instance [Subsingleton K] : Subsingleton (EdgeLabelling G K) :=
  Pi.instSubsingleton

instance [Unique K] : Unique (EdgeLabelling G K) :=
  Pi.unique

instance EdgeLabelling.uniqueOfSubsingleton [Subsingleton V] : Unique (EdgeLabelling G K) :=
  Pi.uniqueOfIsEmpty _

/--
An edge labelling of the complete graph on `V` with labels in type `K`. Sometimes this is called an
edge-colouring, but we reserve that terminology for labellings where incident edges cannot share a
label.
-/
abbrev TopEdgeLabelling (V : Type*) (K : Type*) :=
  EdgeLabelling (⊤ : SimpleGraph V) K

theorem card_EdgeLabelling [DecidableEq V] [Fintype V] [Fintype K] :
    card (TopEdgeLabelling V K) = card K ^ (card V).choose 2 :=
  Fintype.card_fun.trans (by rw [card_top_edgeSet])

namespace EdgeLabelling

/--
Convenience function to get the colour of the edge `x ~ y` in the colouring of the complete graph
on `V`.
-/
def get (C : EdgeLabelling G K) (x y : V) (h : G.Adj x y) : K :=
  C ⟨s(x, y), h⟩

variable {C : EdgeLabelling G K}

theorem get_swap (x y : V) (h : G.Adj x y) : C.get y x h.symm = C.get x y h := by
  simp only [EdgeLabelling.get, Sym2.eq_swap]

@[ext]
theorem ext_get {C' : EdgeLabelling G K}
    (h : ∀ x y, (h : G.Adj x y) → C.get x y h = C'.get x y h) : C = C' := by
  refine funext fun ⟨e, he⟩ => ?_ -- regression in ext
  induction e using Sym2.inductionOn
  exact h _ _ he

/-- Compose an edge-labelling with a function on the colour set.
-/
def compRight (C : EdgeLabelling G K) (f : K → K') : EdgeLabelling G K' :=
  f ∘ C

/-- Compose an edge-labelling with a graph embedding. -/
def pullback (C : EdgeLabelling G K) (f : G' ↪g G) : EdgeLabelling G' K :=
  C ∘ f.mapEdgeSet

@[simp]
theorem pullback_apply {f : G' ↪g G} e :
    C.pullback f e = C (f.mapEdgeSet e) :=
  rfl

@[simp]
theorem pullback_get {f : G' ↪g G} (x y) (h : G'.Adj x y) :
    (C.pullback f).get x y h = C.get (f x) (f y) (by simpa) :=
  rfl

@[simp]
theorem compRight_apply (f : K → K') (e) : C.compRight f e = f (C e) :=
  rfl

@[simp]
theorem compRight_get (f : K → K') (x y) (h : G.Adj x y) :
    (C.compRight f).get x y h = f (C.get x y h) :=
  rfl

attribute [scoped instance] Sym2.Rel.setoid in
/-- Construct an edge labelling from a symmetric function taking values everywhere except the
diagonal.
-/
def mk (f : ∀ x y : V, G.Adj x y → K)
    (f_symm : ∀ (x y : V) (H : G.Adj x y), f y x H.symm = f x y H) : EdgeLabelling G K :=
  fun ⟨e, he⟩ => by
    -- Regression: The weaker Lean 4 code generator here is annoying
    revert he
    refine Quotient.hrecOn e (fun xy => f xy.1 xy.2) ?_
    rintro ⟨a, b⟩ ⟨c, d⟩ ⟨⟩
    · rfl
    refine Function.hfunext ?_ ?_
    ext
    · simp only [adj_comm]
    intro h₁ h₂ _
    exact heq_of_eq (f_symm _ _ _)

theorem mk_get (f : ∀ x y : V, G.Adj x y → K) (f_symm) (x y : V) (h : G.Adj x y) :
    (EdgeLabelling.mk f f_symm).get x y h = f x y h :=
  rfl

/-- `χ.MonochromaticOf m c` says that every edge in `m` is assigned the colour `c` by `m`. -/
def MonochromaticOf (C : EdgeLabelling G K) (m : Set V) (c : K) : Prop :=
  ∀ ⦃x⦄, x ∈ m → ∀ ⦃y⦄, y ∈ m → (h : G.Adj x y) → C.get x y h = c

theorem monochromaticOf_iff_pairwise [DecidableRel G.Adj] (C : EdgeLabelling G K) {m : Set V}
    {c : K} :
    C.MonochromaticOf m c ↔ m.Pairwise fun x y => ∀ h : G.Adj x y, C.get x y h = c := by
  refine forall₄_congr fun _ _ _ _ => ⟨fun _ _ => by simpa , fun ne ad => ?_⟩
  simp only [ne_eq] at ne
  exact (ne (G.ne_of_adj ad)) ad

/--
Given an edge labelling and a choice of label `k`, construct the graph corresponding to the edges
labelled `k`.
-/
def labelGraph (C : EdgeLabelling G K) (k : K) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {e | ∃ h : e ∈ G.edgeSet, C ⟨e, h⟩ = k}

theorem labelGraph_adj {C : EdgeLabelling G K} {k : K} (x y : V) :
    (C.labelGraph k).Adj x y ↔ ∃ H : G.Adj x y, C ⟨s(x, y), H⟩ = k := by
  rw [EdgeLabelling.labelGraph]
  simp only [mem_edgeSet, fromEdgeSet_adj, Set.mem_setOf_eq, Ne.eq_def]
  apply and_iff_left_of_imp _
  rintro ⟨h, -⟩
  exact h.ne

instance [DecidableRel G.Adj] [DecidableEq K] (k : K) {C : EdgeLabelling G K} :
    DecidableRel (C.labelGraph k).Adj := fun _ _ =>
  decidable_of_iff' _ (EdgeLabelling.labelGraph_adj _ _)

theorem labelGraph_le (C : EdgeLabelling G K) {k : K} : C.labelGraph k ≤ G := by
  intro x y
  rw [EdgeLabelling.labelGraph_adj]
  rintro ⟨h, -⟩
  exact h

theorem pairwiseDisjoint {C : EdgeLabelling G K} :
    Set.PairwiseDisjoint (Set.univ : Set K) C.labelGraph := by
  intro k₁ hk₁ k₂ _ h
  simp only [Function.onFun, disjoint_left, EdgeLabelling.labelGraph_adj, not_exists,
    forall_exists_index]
  rintro x y h rfl _
  exact h

theorem iSup_labelGraph (C : EdgeLabelling G K) : (⨆ k : K, C.labelGraph k) = G := by
  ext x y
  simp only [iSup_adj, EdgeLabelling.labelGraph_adj]
  constructor
  · rintro ⟨k, h, rfl⟩
    exact h
  intro h
  exact ⟨_, h, rfl⟩

theorem sup_labelGraph [Fintype K] (C : EdgeLabelling G K) : univ.sup C.labelGraph = G :=
  (C.iSup_labelGraph.symm.trans (by ext; simp)).symm

end EdgeLabelling

namespace TopEdgeLabelling
/-- Compose an edge-labelling, by an injection into the vertex type. This must be an injection, else
we don't know how to colour `x ~ y` in the case `f x = f y`.
-/
abbrev pullback (C : TopEdgeLabelling V K) (f : V' ↪ V) : TopEdgeLabelling V' K :=
  EdgeLabelling.pullback C ⟨f, by simp⟩

@[simp]
lemma monochromaticOf_iff_ne_of_adj (C : TopEdgeLabelling V K) (m : Set V) (c : K) :
C.MonochromaticOf m c ↔ ∀ ⦃x⦄, x ∈ m → ∀ ⦃y⦄, y ∈ m → (h : x ≠ y) → C.get x y h = c := by
  simp_rw [← top_adj]; exact rfl.to_iff

@[simp]
theorem labelGraph_adj {C : TopEdgeLabelling V K} {k : K} (x y : V) :
    (C.labelGraph k).Adj x y ↔ ∃ H : x ≠ y, C.get x y H = k := by
  rw [EdgeLabelling.labelGraph_adj]
  simp
  rfl

end TopEdgeLabelling

/--
From a simple graph on `V`, construct the edge labelling on the complete graph of `V` given where
edges are labelled `1` and non-edges are labelled `0`.
-/
def toTopEdgeLabelling (G : SimpleGraph V) [DecidableRel G.Adj] : TopEdgeLabelling V (Fin 2) :=
  EdgeLabelling.mk (fun x y _ => if G.Adj x y then 1 else 0) fun x y _ => by
    simp only [G.adj_comm]

@[simp]
theorem toTopEdgeLabelling_get {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V} (H : x ≠ y) :
    G.toTopEdgeLabelling.get x y H = if G.Adj x y then 1 else 0 :=
  rfl

theorem toTopEdgeLabelling_labelGraph (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.toTopEdgeLabelling.labelGraph 1 = G := by ext x y; simpa [imp_false] using G.ne_of_adj

theorem toTopEdgeLabelling_labelGraph_compl (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.toTopEdgeLabelling.labelGraph 0 = Gᶜ := by ext x y; simp [imp_false]

theorem TopEdgeLabelling.labelGraph_toTopEdgeLabelling [DecidableEq V]
    (C : TopEdgeLabelling V (Fin 2)) : (C.labelGraph 1).toTopEdgeLabelling = C := by
  refine EdgeLabelling.ext_get ?_
  intro x y h
  simp only [Ne.eq_def, toTopEdgeLabelling_get, TopEdgeLabelling.labelGraph_adj]
  split_ifs with h_1
  · rw [← h_1.choose_spec]
  exact (Fin.fin_two_eq_zero_of_ne_one ((not_exists.mp h_1) h)).symm

instance [DecidableEq K] [DecidableEq V] [DecidableRel G.Adj] (C : EdgeLabelling G K) (m : Finset V)
    (c : K) : Decidable (C.MonochromaticOf m c) :=
  decidable_of_iff' _ C.monochromaticOf_iff_pairwise

namespace EdgeLabelling

variable {m : Set V} {c : K} {C : EdgeLabelling G K}


@[simp] theorem monochromaticOf_empty : C.MonochromaticOf ∅ c := nofun

@[simp]
theorem monochromaticOf_singleton {x : V} : C.MonochromaticOf {x} c := by
  simp [MonochromaticOf]

theorem monochromatic_finset_singleton {x : V} : C.MonochromaticOf ({x} : Finset V) c := by
  simp [MonochromaticOf]

theorem monochromatic_subsingleton (hm : m.Subsingleton) : C.MonochromaticOf m c :=
  fun _ hx _ hy h => (h.ne (hm hx hy)).elim

theorem monochromatic_subsingleton_colours [Subsingleton K] : C.MonochromaticOf m c :=
  fun _ _ _ _ _ => Subsingleton.elim _ _

theorem MonochromaticOf.compRight (e : K → K') (h : C.MonochromaticOf m c) :
    (C.compRight e).MonochromaticOf m (e c) := fun x hx y hy h' => by
  rw [EdgeLabelling.compRight_get, h hx hy h']

theorem monochromaticOf_injective (e : K → K') (he : Function.Injective e) :
    (C.compRight e).MonochromaticOf m (e c) ↔ C.MonochromaticOf m c :=
  forall₅_congr fun x _ y _ h' => by simp [he.eq_iff]

theorem MonochromaticOf.subset {m' : Set V} (h' : m' ⊆ m) (h : C.MonochromaticOf m c) :
    C.MonochromaticOf m' c := fun _ hx _ hy h'' => h (h' hx) (h' hy) h''

theorem MonochromaticOf.image {C : EdgeLabelling G' K} {f : G ↪g G'}
    (h : (C.pullback f).MonochromaticOf m c) : C.MonochromaticOf (f '' m) c := by
  simpa [EdgeLabelling.MonochromaticOf]

theorem MonochromaticOf.map {C : EdgeLabelling G' K} {f : G ↪g G'} {m : Finset V}
    (h : (C.pullback f).MonochromaticOf m c) : C.MonochromaticOf (m.map f.toEmbedding) c := by
  rw [coe_map]
  exact h.image


/-- The predicate `χ.MonochromaticBetween X Y k` says every edge between `X` and `Y` is labelled
`k` by the labelling `χ`. -/
def MonochromaticBetween (C : EdgeLabelling G K) (X Y : Set V) (k : K) : Prop :=
  ∀ ⦃x⦄, x ∈ X → ∀ ⦃y⦄, y ∈ Y → (h : G.Adj x y) → C.get x y h = k

instance [DecidableEq V] [DecidableEq K] [DecidableRel G.Adj] {X Y : Finset V} {k : K} :
    Decidable (MonochromaticBetween C X Y k) := by
  simp only [MonochromaticBetween, mem_coe]
  exact Multiset.decidableForallMultiset

@[simp]
theorem monochromaticBetween_empty_left {Y : Set V} {k : K} : C.MonochromaticBetween ∅ Y k := by
  simp [MonochromaticBetween]

@[simp]
theorem monochromaticBetween_empty_right {X : Set V} {k : K} :
    C.MonochromaticBetween X ∅ k := by
  simp [MonochromaticBetween]

theorem monochromaticBetween_singleton_left {x : V} {Y : Set V} {k : K} :
    C.MonochromaticBetween {x} Y k ↔ ∀ ⦃y⦄, y ∈ Y → (h : G.Adj x y) → C.get x y h = k := by
  simp [MonochromaticBetween]

theorem monochromaticBetween_singleton_right {y : V} {X : Set V} {k : K} :
    C.MonochromaticBetween X {y} k ↔ ∀ ⦃x⦄, x ∈ X → (h : G.Adj x y) → C.get x y h = k := by
  simp [MonochromaticBetween]

theorem monochromaticBetween_union_left [DecidableEq V] {X Y Z : Set V} {k : K} :
    C.MonochromaticBetween (X ∪ Y) Z k ↔
      C.MonochromaticBetween X Z k ∧ C.MonochromaticBetween Y Z k :=
  by simp only [MonochromaticBetween, Set.mem_union, or_imp, forall_and]

theorem monochromaticBetween_union_right [DecidableEq V] {X Y Z : Set V} {k : K} :
    C.MonochromaticBetween X (Y ∪ Z) k ↔
      C.MonochromaticBetween X Y k ∧ C.MonochromaticBetween X Z k :=
  by simp only [MonochromaticBetween, Set.mem_union, or_imp, forall_and]

theorem monochromaticBetween_self {X : Set V} {k : K} :
    C.MonochromaticBetween X X k ↔ C.MonochromaticOf X k := by
  simp only [MonochromaticBetween, MonochromaticOf]

theorem MonochromaticBetween.subset_left {X Y Z : Set V} {k : K}
    (hYZ : C.MonochromaticBetween Y Z k) (hXY : X ⊆ Y) : C.MonochromaticBetween X Z k :=
  fun _ hx _ hy _ => hYZ (hXY hx) hy _

theorem MonochromaticBetween.subset_right {X Y Z : Set V} {k : K}
    (hXZ : C.MonochromaticBetween X Z k) (hXY : Y ⊆ Z) : C.MonochromaticBetween X Y k :=
  fun _ hx _ hy _ => hXZ hx (hXY hy) _

theorem MonochromaticBetween.subset {W X Y Z : Set V} {k : K}
    (hWX : C.MonochromaticBetween W X k) (hYW : Y ⊆ W) (hZX : Z ⊆ X) :
    C.MonochromaticBetween Y Z k := fun _ hx _ hy _ => hWX (hYW hx) (hZX hy) _

theorem MonochromaticBetween.image {C : EdgeLabelling G' K} {X Y : Set V} {k : K} {f : G ↪g G'}
    (hXY : (C.pullback f).MonochromaticBetween X Y k) :
    C.MonochromaticBetween (f '' X) (f '' Y) k := by
  simpa [MonochromaticBetween]

theorem MonochromaticBetween.symm {X Y : Set V} {k : K} (hXY : C.MonochromaticBetween X Y k) :
    C.MonochromaticBetween Y X k :=
  fun y hy x hx h => by rw [get_swap _ _ h.symm]; exact hXY hx hy _

theorem MonochromaticBetween.comm {X Y : Set V} {k : K} :
    C.MonochromaticBetween Y X k ↔ C.MonochromaticBetween X Y k :=
  ⟨MonochromaticBetween.symm, MonochromaticBetween.symm⟩

theorem monochromaticOf_union {X Y : Set V} {k : K} :
    C.MonochromaticOf (X ∪ Y) k ↔
      C.MonochromaticOf X k ∧ C.MonochromaticOf Y k ∧ C.MonochromaticBetween X Y k := by
  rw [← and_iff_left_of_imp MonochromaticBetween.symm]
  simp only [MonochromaticOf, Set.mem_union, or_imp, forall_and, MonochromaticBetween]
  tauto

theorem monochromaticOf_insert [DecidableEq V] {y : V} :
    C.MonochromaticOf (insert y m) c ↔ C.MonochromaticOf m c ∧ C.MonochromaticBetween m {y} c := by
  rw [Set.insert_eq, ← coe_singleton, Set.union_comm]
  convert monochromaticOf_union
  simp only [coe_singleton, monochromaticOf_singleton, true_and]

end EdgeLabelling

theorem TopEdgeLabelling.monochromaticOf_insert [DecidableEq V] {C : TopEdgeLabelling V K} {c : K}
    {m : Set V} {x : V} (hx : x ∉ m) : C.MonochromaticOf (insert x m) c ↔
    C.MonochromaticOf m c ∧ ∀ ⦃y⦄, (H : y ∈ m) → C.get x y (H.ne_of_notMem hx).symm = c := by
  rw [Set.insert_eq, ← coe_singleton, Set.union_comm]
  convert EdgeLabelling.monochromaticOf_union
  simp
  simp [EdgeLabelling.MonochromaticBetween]
  constructor
  · intros a y ym _
    rw [EdgeLabelling.get_swap]
    exact a ym
  · intros a y ym
    rw [EdgeLabelling.get_swap]
    exact a ym (ne_of_mem_of_not_mem ym hx)

theorem TopEdgeLabelling.Disjoint.monochromaticBetween {C : TopEdgeLabelling V K} {X Y : Set V}
    {k : K} (h : Disjoint X Y) : C.MonochromaticBetween X Y k ↔
      ∀ ⦃x⦄, (hx : x ∈ X) → ∀ ⦃y⦄, (hy : y ∈ Y) → C.get x y (h.ne_of_mem hx hy) = k :=
  forall₄_congr fun x hx y hy => by simp [h.ne_of_mem hx hy]

open EdgeLabelling

variable {C : TopEdgeLabelling V K}


-- TODO (BM): I think the `∃` part of this should be its own def...
/-- The predicate `is_ramsey_valid V n` says that the type `V` is large enough to guarantee a
clique of size `n k` for some colour `k : K`.
-/
def IsRamseyValid (V : Type*) (n : K → ℕ) : Prop :=
  ∀ C : TopEdgeLabelling V K, ∃ (m : Finset V) (c : _), C.MonochromaticOf m c ∧ n c ≤ m.card

theorem IsRamseyValid.empty_colours [IsEmpty K] {n : K → ℕ} : IsRamseyValid (Fin 2) n := fun C =>
  isEmptyElim (C.get 0 1 (by norm_num))

theorem IsRamseyValid.exists_zero_of_isEmpty [IsEmpty V] {n : K → ℕ} (h : IsRamseyValid V n) :
    ∃ c, n c = 0 :=
  let ⟨m, c, _, hc⟩ := h isEmptyElim
  ⟨c, by simpa [Subsingleton.elim m ∅] using hc⟩

theorem isRamseyValid_of_zero {n : K → ℕ} (c : K) (hc : n c = 0) : IsRamseyValid V n := fun C =>
  ⟨∅, c, by simp, by simp [hc]⟩

theorem isRamseyValid_of_exists_zero (n : K → ℕ) (h : ∃ c, n c = 0) : IsRamseyValid V n :=
  let ⟨_, hc⟩ := h
  isRamseyValid_of_zero _ hc

theorem IsRamseyValid.mono_right {n n' : K → ℕ} (h : n ≤ n') (h' : IsRamseyValid V n') :
    IsRamseyValid V n := fun C =>
  let ⟨m, c, hc, hm⟩ := h' C
  ⟨m, c, hc, hm.trans' (h _)⟩

theorem isRamseyValid_iff_eq {n : K → ℕ} :
    IsRamseyValid V n ↔
      ∀ C : TopEdgeLabelling V K, ∃ (m : Finset V) (c : K),
        C.MonochromaticOf m c ∧ n c = m.card := by
  refine forall_congr' fun C => ?_
  rw [exists_comm, @exists_comm (Finset V)]
  refine exists_congr fun c => ?_
  constructor
  · rintro ⟨a, ha, ha'⟩
    obtain ⟨b, hb, hb'⟩ := exists_subset_card_eq ha'
    exact ⟨b, ha.subset hb, hb'.symm⟩
  · rintro ⟨a, ha, ha'⟩
    exact ⟨_, ha, ha'.le⟩

theorem isRamseyValid_iff_embedding_aux {n : ℕ} (c : K) :
    (∃ m : Finset V, C.MonochromaticOf m c ∧ n = m.card) ↔
      Nonempty ((⊤ : SimpleGraph (Fin n)) ↪g C.labelGraph c) := by
  constructor
  · rintro ⟨m, hm, hm'⟩
    have : Fintype.card m = n := by rw [Fintype.card_coe, hm']
    classical
    obtain ⟨e⟩ := Fintype.truncEquivFinOfCardEq this
    refine ⟨⟨e.symm.toEmbedding.trans (Function.Embedding.subtype _), ?_⟩⟩
    intro a b
    simp only [Ne.eq_def, Function.Embedding.trans_apply, Equiv.coe_toEmbedding,
      Function.Embedding.coe_subtype, labelGraph_adj, top_adj, ← Subtype.ext_iff,
      EmbeddingLike.apply_eq_iff_eq]
    constructor
    · rintro ⟨h, -⟩
      exact h
    intro h
    exact ⟨h, hm (e.symm a).prop (e.symm b).prop _⟩
  rintro ⟨f⟩
  refine ⟨(univ : Finset (Fin n)).map f.toEmbedding, ?_, ?_⟩
  · rw [TopEdgeLabelling.monochromaticOf_iff_ne_of_adj]
    simp only [Ne.eq_def, RelEmbedding.inj, coe_map, RelEmbedding.coe_toEmbedding, Set.mem_image,
      coe_univ, Set.mem_univ, true_and, forall_exists_index, forall_apply_eq_imp_iff]
    intro x y h
    have : (⊤ : SimpleGraph (Fin n)).Adj x y := h
    simpa [-top_adj, ←f.map_rel_iff, h, RelEmbedding.inj] using this
      -- this simpa needs more help than in lean 3
  rw [card_map, card_fin]

-- BM: pretty good chance this is a better definition...
-- it also generalises better to induced ramsey numbers of graphs
-- and if you transfer with `top_hom_graph_equiv` you get ramsey numbers of graphs
theorem isRamseyValid_iff_embedding {n : K → ℕ} :
    IsRamseyValid V n ↔
      ∀ C : TopEdgeLabelling V K,
        ∃ c : K, Nonempty ((⊤ : SimpleGraph (Fin (n c))) ↪g C.labelGraph c) := by
  rw [isRamseyValid_iff_eq]
  refine forall_congr' fun C => ?_
  rw [exists_comm]
  simp only [isRamseyValid_iff_embedding_aux]

theorem IsRamseyValid.embedding {n : K → ℕ} (f : V ↪ V') (h' : IsRamseyValid V n) :
    IsRamseyValid V' n := fun C =>
  let ⟨m', c, hc, hm'⟩ := h' (C.pullback f)
  ⟨m'.map f, c, by simpa only [coe_map] using hc.image, hm'.trans_eq (card_map _).symm⟩

theorem IsRamseyValid.card_fin [Fintype V] {N : ℕ} {n : K → ℕ} (h : N ≤ card V)
    (h' : IsRamseyValid (Fin N) n) : IsRamseyValid V n :=
  h'.embedding <| (Fin.castLEOrderEmb h).toEmbedding.trans (Fintype.equivFin V).symm

theorem IsRamseyValid.equiv_left (n : K → ℕ) (f : V ≃ V') :
    IsRamseyValid V n ↔ IsRamseyValid V' n :=
  ⟨fun h => h.embedding f, fun h => h.embedding f.symm⟩

theorem IsRamseyValid.equiv_right {n : K → ℕ} (f : K' ≃ K) (h : IsRamseyValid V n) :
    IsRamseyValid V (n ∘ f) := fun C =>
  let ⟨m, c, hm, hc⟩ := h (C.compRight f)
  ⟨m, f.symm c, by rwa [← monochromaticOf_injective f f.injective, f.apply_symm_apply], by
    simpa using hc⟩

theorem isRamseyValid_equiv_right {n : K → ℕ} (f : K' ≃ K) :
    IsRamseyValid V (n ∘ f) ↔ IsRamseyValid V n :=
  ⟨fun h => by convert h.equiv_right f.symm; ext; simp, fun h => h.equiv_right _⟩

instance [DecidableEq K] [Fintype K] [DecidableEq V] [Fintype V] (n : K → ℕ) :
    Decidable (IsRamseyValid V n) :=
  Fintype.decidableForallFintype

theorem ramsey_base [Nonempty V] {n : K → ℕ} (hn : ∃ k, n k ≤ 1) : IsRamseyValid V n :=
  by
  inhabit V
  obtain ⟨k, hk⟩ := hn
  exact fun C => ⟨{Inhabited.default}, k, monochromatic_finset_singleton, by simpa using hk⟩

theorem ramsey_base' [Fintype V] (n : K → ℕ) (hn : ∃ k, n k ≤ 1) (hV : 1 ≤ card V) :
    IsRamseyValid V n :=
  @ramsey_base _ _ (Fintype.card_pos_iff.1 hV) _ hn

theorem isRamseyValid_min [Fintype V] [Nonempty K] {n : K → ℕ} {n' : ℕ} (h : IsRamseyValid V n)
    (hn : ∀ k, n' ≤ n k) : n' ≤ card V :=
  let ⟨m, _, _, hm⟩ := h (Classical.arbitrary (TopEdgeLabelling V K))
  (hn _).trans (hm.trans (Finset.card_le_univ m))

theorem isRamseyValid_unique [Fintype V] [Unique K] {n : K → ℕ} (hV : n default ≤ card V) :
    IsRamseyValid V n := fun C => ⟨univ, default, monochromatic_subsingleton_colours, by simpa⟩

theorem IsRamseyValid.remove_twos {n : K → ℕ} (h : IsRamseyValid V n) :
    IsRamseyValid V fun k : { k : K // n k ≠ 2 } => n k := by
  cases isEmpty_or_nonempty V
  · obtain ⟨c, hc⟩ := h.exists_zero_of_isEmpty
    exact isRamseyValid_of_zero ⟨c, by simp [hc]⟩ hc
  by_cases h' : ∃ k, n k ≤ 1
  · obtain ⟨k, hk⟩ := h'
    refine ramsey_base ⟨⟨k, ?_⟩, hk⟩
    linarith
  simp only [not_exists, not_le, Nat.lt_iff_add_one_le] at h'
  intro C
  obtain ⟨m, c, hm, hc⟩ := h (C.compRight Subtype.val)
  have : 1 < m.card := (h' c).trans hc
  rw [Finset.one_lt_card_iff] at this
  obtain ⟨a, b, ha, hb, hab⟩ := this
  have : Subtype.val (C.get a b hab) = c := hm ha hb hab
  refine ⟨m, _, ?_, hc.trans_eq' (congr_arg n this)⟩
  rwa [← monochromaticOf_injective _ Subtype.val_injective, this]

theorem IsRamseyValid.of_remove_twos {n : K → ℕ}
    (h : IsRamseyValid V fun k : { k : K // n k ≠ 2 } => n k) : IsRamseyValid V n :=
  by
  intro C
  classical
  by_cases h'' : ∃ (x y : V) (H : x ≠ y), n (C.get x y H) = 2
  · obtain ⟨x, y, H, hxy⟩ := h''
    refine ⟨({x, y} : Finset V), C.get x y H, ?_, ?_⟩
    · rw [coe_pair, monochromaticOf_insert]
      refine ⟨monochromaticOf_singleton, ?_⟩
      simp [MonochromaticBetween, Set.mem_singleton_iff]
      exact fun _ => get_swap x y H
    rw [hxy, card_pair H]
  push_neg at h''
  let C' : TopEdgeLabelling V { k : K // n k ≠ 2 } :=
    EdgeLabelling.mk (fun x y h => ⟨C.get x y h, h'' _ _ h⟩) ?_
  swap
  · intro x y h
    ext
    dsimp
    exact get_swap _ _ _
  obtain ⟨m, c, hm, hc⟩ := h C'
  refine ⟨m, c, ?_, hc⟩
  intro x hx y hy h
  exact Subtype.ext_iff.1 (hm hx hy h)

theorem isRamseyValid_iff_remove_twos (n : K → ℕ) :
    (IsRamseyValid V fun k : { k : K // n k ≠ 2 } => n k) ↔ IsRamseyValid V n :=
  ⟨IsRamseyValid.of_remove_twos, IsRamseyValid.remove_twos⟩

theorem isRamseyValid_two {n : K → ℕ} {n' : K' → ℕ} (f : K' → K)
    (hf : ∀ x : K', n' x ≠ 2 → n (f x) ≠ 2)
    (hf_inj : ∀ x y : K', n' x ≠ 2 → n' y ≠ 2 → f x = f y → x = y)
    (hf_surj : ∀ x : K, n x ≠ 2 → ∃ y : K', n' y ≠ 2 ∧ f y = x)
    (hf_comm : ∀ x : K', n' x ≠ 2 → n (f x) = n' x) : IsRamseyValid V n' ↔ IsRamseyValid V n :=
  by
  let e : { k // n' k ≠ 2 } → { k // n k ≠ 2 } := fun k => ⟨f k, hf _ k.prop⟩
  have he : Function.Injective e := fun a b h =>
    Subtype.ext (hf_inj _ _ a.prop b.prop (Subtype.ext_iff.1 h))
  have he' : Function.Surjective e := by
    rintro ⟨i, hi⟩
    simpa [e] using hf_surj i hi
  rw [← isRamseyValid_iff_remove_twos n, ← isRamseyValid_iff_remove_twos n', ←
    isRamseyValid_equiv_right (Equiv.ofBijective e ⟨he, he'⟩)]
  congr! 2 with ⟨k, hk⟩
  exact (hf_comm _ hk).symm

open scoped BigOperators

variable [DecidableEq K'] [Fintype K'] {n : K → ℕ}

theorem ramsey_fin_induct_aux {V : Type*} [DecidableEq K] {n : K → ℕ} (N : K → ℕ)
    {C : TopEdgeLabelling V K} (m : K → Finset V) (x : V)
    (hN : ∀ k, IsRamseyValid (Fin (N k)) (Function.update n k (n k - 1))) (hx : ∀ k, x ∉ m k)
    (h : ∃ k, N k ≤ (m k).card)
    (hm : ∀ (k) (y : V) (hy : y ∈ m k), C.get x y (ne_of_mem_of_not_mem hy (hx k)).symm = k) :
    ∃ (m : Finset V) (c : _), C.MonochromaticOf m c ∧ n c ≤ m.card := by
  classical
  obtain ⟨k, hk⟩ := h
  have : IsRamseyValid (m k) (Function.update n k (n k - 1)) := (hN k).card_fin (by simp [hk])
  obtain ⟨m', k', hm', hk'⟩ := this (C.pullback (Function.Embedding.subtype _))
  rcases ne_or_eq k k' with (hk | rfl)
  · exact ⟨_, _, hm'.map, by simpa [hk.symm] using hk'⟩
  refine ⟨insert (x : V) (m'.map (Function.Embedding.subtype _)), k, ?_, ?_⟩
  · rw [coe_insert, monochromaticOf_insert]
    refine ⟨hm'.map, ?_⟩
    simp only [MonochromaticBetween, coe_map, Function.Embedding.subtype_apply, Set.mem_image,
      mem_coe, Subtype.exists, exists_and_right, exists_eq_right, Set.mem_singleton_iff, top_adj,
      ne_eq, forall_eq, forall_exists_index]
    intros y ym _ _
    rw [get_swap]
    exact hm k y ym
  have : x ∉ (m'.map (Function.Embedding.subtype _) : Set V) := by simp [hx k]
  rw [card_insert_of_notMem this, card_map, ← tsub_le_iff_right]
  rwa [Function.update_self] at hk'

theorem ramsey_fin_induct [DecidableEq K] [Fintype K] (n : K → ℕ) (N : K → ℕ)
    (hN : ∀ k, IsRamseyValid (Fin (N k)) (Function.update n k (n k - 1))) :
    IsRamseyValid (Fin (∑ k, (N k - 1) + 2)) n := by
  by_cases h : ∃ k, n k ≤ 1
  · refine ramsey_base' _ h ?_
    rw [Fintype.card_fin]
    exact (Nat.le_add_left _ _).trans' (by norm_num)
  push_neg at h
  have hN' : ∀ k, 1 ≤ N k := by
    intro k
    by_contra!
    have : IsEmpty (Fin (N k)) :=
      by
      rw [← Fintype.card_eq_zero_iff, Fintype.card_fin]
      simpa only [Nat.lt_one_iff] using this
    obtain ⟨k', hk'⟩ := (hN k).exists_zero_of_isEmpty
    rcases eq_or_ne k k' with (rfl | hk)
    · simp only [Function.update_self, tsub_eq_zero_iff_le] at hk'
      exact hk'.not_gt (h _)
    rw [Function.update_of_ne hk.symm] at hk'
    simpa only [not_lt_zero'] using (h k').trans_eq hk'
  classical
  set V := Fin (∑ k, (N k - 1) + 2)
  intro C
  let x : V := 0
  let m : K → Finset V := fun k => neighborFinset (C.labelGraph k) x
  have : univ.biUnion m = {x}ᶜ := by
    simp only [← Finset.coe_inj, coe_biUnion, mem_coe, mem_univ, Set.iUnion_true, coe_compl,
      coe_singleton, coe_neighborFinset, m]
    rw [← neighborSet_iSup, EdgeLabelling.iSup_labelGraph C, neighborSet_top]
  have e : ∑ k, (m k).card = ∑ k, (N k - 1) + 1 :=
    by
    rw [← card_biUnion, this, card_compl, ← card_univ, card_fin, card_singleton,
      Nat.add_succ_sub_one]
    rintro x _ y _ h
    refine neighborFinset_disjoint ?_
    exact EdgeLabelling.pairwiseDisjoint (by simp) (by simp) h
  have : ∃ k, N k - 1 < (m k).card := by
    by_contra!
    have : ∑ k, (m k).card ≤ ∑ k, (N k - 1) := sum_le_sum fun k _ => this k
    rw [e] at this
    simp only [add_le_iff_nonpos_right, le_zero_iff, Nat.one_ne_zero] at this
  obtain ⟨k, hk⟩ := this
  rw [tsub_lt_iff_right (hN' _), Nat.lt_add_one_iff] at hk
  refine ramsey_fin_induct_aux _ m x hN ?_ ⟨k, hk⟩ ?_
  · simp [m]
  · simp [m]

theorem ramsey_fin_exists [Finite K] (n : K → ℕ) : ∃ N, IsRamseyValid (Fin N) n := by
  classical
  refine @WellFoundedLT.induction _ _ _ (fun a => ∃ N, IsRamseyValid (Fin N) a) n ?_
  clear n
  intro n ih
  by_cases h : ∃ k, n k = 0
  · exact ⟨0, isRamseyValid_of_exists_zero _ h⟩
  push_neg at h
  dsimp at ih
  have : ∀ k, Function.update n k (n k - 1) < n :=
    by
    simp only [update_lt_self_iff]
    intro k
    exact Nat.pred_lt (h k)
  have := fun k => ih _ (this k)
  choose N hN using this
  cases nonempty_fintype K
  exact ⟨_, ramsey_fin_induct _ _ hN⟩

-- hn can be weakened but it's just a nontriviality assumption
theorem ramsey_fin_induct' [DecidableEq K] [Fintype K] (n : K → ℕ) (N : K → ℕ) (hn : ∀ k, 2 ≤ n k)
    (hN : ∀ k, IsRamseyValid (Fin (N k)) (Function.update n k (n k - 1))) :
    IsRamseyValid (Fin (∑ k, N k + 2 - card K)) n := by
  have hN' : ∀ k, 1 ≤ N k := by
    intro k
    by_contra!
    have : IsEmpty (Fin (N k)) :=
      by
      rw [← Fintype.card_eq_zero_iff, Fintype.card_fin]
      simpa only [Nat.lt_one_iff] using this
    obtain ⟨k', hk'⟩ := (hN k).exists_zero_of_isEmpty
    rcases eq_or_ne k k' with (rfl | hk)
    · simp only [Function.update_self, tsub_eq_zero_iff_le] at hk'
      exact hk'.not_gt (hn _)
    rw [Function.update_of_ne hk.symm] at hk'
    simpa only [nonpos_iff_eq_zero, OfNat.ofNat_ne_zero] using (hn k').trans_eq hk'
  have h : ∀ x : K, x ∈ (univ : Finset K) → 1 ≤ N x := by simpa using hN'
  have := ramsey_fin_induct n N hN
  rwa [sum_tsub _ h, tsub_add_eq_add_tsub, ← Fintype.card_eq_sum_ones] at this
  exact sum_le_sum h

open Matrix (vecCons)

theorem ramsey_fin_induct_two {i j Ni Nj : ℕ} (hi : 2 ≤ i) (hj : 2 ≤ j)
    (hi' : IsRamseyValid (Fin Ni) ![i - 1, j]) (hj' : IsRamseyValid (Fin Nj) ![i, j - 1]) :
    IsRamseyValid (Fin (Ni + Nj)) ![i, j] := by
  have : ∑ z : Fin 2, ![Ni, Nj] z + 2 - card (Fin 2) = Ni + Nj := by simp
  have h := ramsey_fin_induct' ![i, j] ![Ni, Nj] ?_ ?_
  · rwa [this] at h
  · rw [Fin.forall_fin_two]
    exact ⟨hi, hj⟩
  · rw [Fin.forall_fin_two, Function.update_head, Function.update_cons_one]
    exact ⟨hi', hj'⟩

theorem ramsey_fin_induct_two_evens {i j Ni Nj : ℕ} (hi : 2 ≤ i) (hj : 2 ≤ j) (hNi : Even Ni)
    (hNj : Even Nj) (hi' : IsRamseyValid (Fin Ni) ![i - 1, j])
    (hj' : IsRamseyValid (Fin Nj) ![i, j - 1]) : IsRamseyValid (Fin (Ni + Nj - 1)) ![i, j] := by
  have hNi' : 1 ≤ Ni := by
    by_contra!
    have : IsEmpty (Fin Ni) :=
      by
      rw [← Fintype.card_eq_zero_iff, Fintype.card_fin]
      simpa only [Nat.lt_one_iff] using this
    obtain ⟨k', hk'⟩ := hi'.exists_zero_of_isEmpty
    revert k'
    simp only [Fin.forall_fin_two, imp_false, Matrix.cons_val_zero, tsub_eq_zero_iff_le, not_le,
      Matrix.cons_val_one]
    exact ⟨hi, by linarith⟩
  have hNj' : 1 ≤ Nj := by
    by_contra!
    have : IsEmpty (Fin Nj) :=
      by
      rw [← Fintype.card_eq_zero_iff, Fintype.card_fin]
      simpa only [Nat.lt_one_iff] using this
    obtain ⟨k', hk'⟩ := hj'.exists_zero_of_isEmpty
    revert k'
    simp only [Fin.forall_fin_two, imp_false, Matrix.cons_val_zero, tsub_eq_zero_iff_le, not_le,
      Matrix.cons_val_one]
    exact ⟨by linarith, hj⟩
  have : Odd (card (Fin (Ni + Nj - 1))) :=
    by
    rw [Fintype.card_fin, Nat.odd_sub (le_add_right hNi')]
    simp [hNi, hNj, parity_simps]
  intro C
  obtain ⟨x, hx⟩ := @exists_even_degree (Fin (Ni + Nj - 1)) (C.labelGraph 0) _ _ this
  let m : Fin 2 → Finset (Fin (Ni + Nj - 1)) := fun k => neighborFinset (C.labelGraph k) x
  change Even (m 0).card at hx
  have : univ.biUnion m = {x}ᶜ :=
    by
    simp only [← Finset.coe_inj, coe_biUnion, mem_coe, mem_univ, Set.iUnion_true, coe_compl,
      coe_singleton, m, coe_neighborFinset]
    rw [← neighborSet_iSup, EdgeLabelling.iSup_labelGraph C, neighborSet_top]
  have e : ∑ k, (m k).card = Ni + Nj - 2 :=
    by
    rw [← card_biUnion, this, card_compl, ← card_univ, card_fin, card_singleton, Nat.sub_sub]
    rintro x _ y _ h
    refine neighborFinset_disjoint ?_
    exact EdgeLabelling.pairwiseDisjoint (by simp) (by simp) h
  have : Ni ≤ (m 0).card ∨ Nj ≤ (m 1).card :=
    by
    have : (m 0).card + 1 ≠ Ni := by
      intro h
      rw [← h] at hNi
        -- regression (maybe temporary): this extra simp is a weirdness with Lean 4 simp/zeta
      simp [hx, parity_simps] at hNi
    rw [eq_tsub_iff_add_eq_of_le (add_le_add hNi' hNj'), Fin.sum_univ_two] at e
    by_contra! h'
    rw [Nat.lt_iff_add_one_le, Nat.lt_iff_add_one_le, le_iff_lt_or_eq, or_iff_left this,
      Nat.lt_iff_add_one_le, add_assoc] at h'
    have := add_le_add h'.1 h'.2
    rw [add_add_add_comm, ← add_assoc, e] at this
    simp only [add_le_iff_nonpos_right, le_zero_iff, Nat.one_ne_zero] at this
  refine ramsey_fin_induct_aux ![Ni, Nj] m x ?_ (by simp [m]) ?_ ?_
  · rw [Fin.forall_fin_two, Function.update_head, Function.update_cons_one]
    exact ⟨hi', hj'⟩
  · rwa [Fin.exists_fin_two]
  · rw [Fin.forall_fin_two]
    simp [m]

theorem ramsey_fin_induct_three {i j k Ni Nj Nk : ℕ} (hi : 2 ≤ i) (hj : 2 ≤ j) (hk : 2 ≤ k)
    (hi' : IsRamseyValid (Fin Ni) ![i - 1, j, k]) (hj' : IsRamseyValid (Fin Nj) ![i, j - 1, k])
    (hk' : IsRamseyValid (Fin Nk) ![i, j, k - 1]) :
    IsRamseyValid (Fin (Ni + Nj + Nk - 1)) ![i, j, k] := by
  have : ∑ k : Fin 3, ![Ni, Nj, Nk] k + 2 - card (Fin 3) = Ni + Nj + Nk - 1 := by
    rw [Fintype.card_fin, Nat.succ_sub_succ_eq_sub, Fin.sum_univ_three]
    rfl
  have h := ramsey_fin_induct' ![i, j, k] ![Ni, Nj, Nk] ?_ ?_
  · rwa [this] at h
  · rw [Fin.forall_fin_succ, Fin.forall_fin_two]
    exact ⟨hi, hj, hk⟩
  · rw [Fin.forall_fin_succ, Fin.forall_fin_two, Function.update_head, Fin.succ_zero_eq_one,
      Fin.succ_one_eq_two, Function.update_cons_one, Function.update_cons_two]
    exact ⟨hi', hj', hk'⟩

variable {N : ℕ} [Fintype V] [DecidableEq K] [Fintype K]

/-- Given a tuple `n : K → ℕ` of naturals indexed by `K`, define the ramsey number as the smallest
`N` such that any labelling of the complete graph on `N` vertices with `K` labels contains a
subset of size `n k` in which every edge is labelled `k`.
While this definition is computable, it is not at all efficient to compute.
-/
def ramseyNumber (n : K → ℕ) : ℕ :=
  Nat.find (ramsey_fin_exists n)

theorem ramseyNumber_spec_fin (n : K → ℕ) : IsRamseyValid (Fin (ramseyNumber n)) n :=
  Nat.find_spec (ramsey_fin_exists n)

theorem ramseyNumber_spec (h : ramseyNumber n ≤ card V) : IsRamseyValid V n :=
  (ramseyNumber_spec_fin n).card_fin h

theorem ramseyNumber_min_fin (hN : IsRamseyValid (Fin N) n) : ramseyNumber n ≤ N :=
  Nat.find_min' (ramsey_fin_exists n) hN

theorem ramseyNumber_min (hN : IsRamseyValid V n) : ramseyNumber n ≤ card V :=
  ramseyNumber_min_fin (hN.embedding (Fintype.equivFin V).toEmbedding)

theorem ramseyNumber_le_iff : ramseyNumber n ≤ card V ↔ IsRamseyValid V n :=
  ⟨ramseyNumber_spec, ramseyNumber_min⟩

theorem ramseyNumber_le_iff_fin : ramseyNumber n ≤ N ↔ IsRamseyValid (Fin N) n :=
  ⟨fun h => (ramseyNumber_spec_fin n).embedding (Fin.castLEOrderEmb h).toEmbedding,
   ramseyNumber_min_fin⟩

theorem ramseyNumber_eq_of (h : IsRamseyValid (Fin (N + 1)) n) (h' : ¬IsRamseyValid (Fin N) n) :
    ramseyNumber n = N + 1 := by
  rw [← ramseyNumber_le_iff_fin] at h h';
  exact h.antisymm (lt_of_not_ge h')

theorem ramseyNumber_congr {n' : K' → ℕ}
    (h : ∀ N, IsRamseyValid (Fin N) n ↔ IsRamseyValid (Fin N) n') :
    ramseyNumber n = ramseyNumber n' :=
  (ramseyNumber_min_fin ((h _).2 (ramseyNumber_spec_fin _))).antisymm
    (ramseyNumber_min_fin ((h _).1 (ramseyNumber_spec_fin _)))

theorem ramseyNumber_equiv (f : K' ≃ K) : ramseyNumber (n ∘ f) = ramseyNumber n :=
  ramseyNumber_congr fun _ => isRamseyValid_equiv_right f

theorem ramseyNumber_first_swap {i : ℕ} (x y : ℕ) (t : Fin i → ℕ) :
    ramseyNumber (vecCons x (vecCons y t)) = ramseyNumber (vecCons y (vecCons x t)) := by
  have : vecCons x (vecCons y t) ∘ Equiv.swap 0 1 = vecCons y (vecCons x t) := by
    rw [Function.swap_cons]
  rw [← this, ramseyNumber_equiv]

theorem ramseyNumber_pair_swap (x y : ℕ) : ramseyNumber ![x, y] = ramseyNumber ![y, x] :=
  ramseyNumber_first_swap _ _ _

theorem ramseyNumber.eq_zero_iff : ramseyNumber n = 0 ↔ ∃ c, n c = 0 := by
  rw [← le_zero_iff, ramseyNumber_le_iff_fin]
  exact ⟨fun h => h.exists_zero_of_isEmpty, isRamseyValid_of_exists_zero _⟩

theorem ramseyNumber.exists_zero_of_eq_zero (h : ramseyNumber n = 0) : ∃ c, n c = 0 :=
  ramseyNumber.eq_zero_iff.1 h

theorem ramseyNumber_exists_zero (c : K) (hc : n c = 0) : ramseyNumber n = 0 :=
  ramseyNumber.eq_zero_iff.2 ⟨c, hc⟩

theorem ramseyNumber_pos : 0 < ramseyNumber n ↔ ∀ c, n c ≠ 0 := by
  rw [pos_iff_ne_zero, Ne.eq_def, ramseyNumber.eq_zero_iff, not_exists]

theorem ramseyNumber_le_one (hc : ∃ c, n c ≤ 1) : ramseyNumber n ≤ 1 := by
  rw [ramseyNumber_le_iff_fin]; exact ramsey_base hc

theorem ramseyNumber_ge_min [Nonempty K] (i : ℕ) (hk : ∀ k, i ≤ n k) : i ≤ ramseyNumber n :=
  (isRamseyValid_min (ramseyNumber_spec_fin n) hk).trans_eq (card_fin _)

theorem exists_le_of_ramseyNumber_le [Nonempty K] (i : ℕ) (hi : ramseyNumber n ≤ i) :
    ∃ k, n k ≤ i := by contrapose! hi; exact ramseyNumber_ge_min (i + 1) hi

@[simp]
theorem ramseyNumber_empty [IsEmpty K] : ramseyNumber n = 2 := by
  refine ramseyNumber_eq_of ?_ ?_
  · exact IsRamseyValid.empty_colours
  simp [IsRamseyValid]

theorem ramseyNumber_nil : ramseyNumber ![] = 2 :=
  ramseyNumber_empty

theorem exists_le_one_of_ramseyNumber_le_one (hi : ramseyNumber n ≤ 1) : ∃ k, n k ≤ 1 :=
  haveI : Nonempty K := by
    rw [← not_isEmpty_iff]
    intro
    rw [ramseyNumber_empty] at hi
    norm_num at hi
  exists_le_of_ramseyNumber_le _ hi

theorem ramseyNumber_eq_one (hc : ∃ c, n c = 1) (hc' : ∀ c, n c ≠ 0) : ramseyNumber n = 1 := by
  obtain ⟨c, hc⟩ := hc
  refine (ramseyNumber_le_one ⟨c, hc.le⟩).antisymm ?_
  rwa [Nat.succ_le_iff, ramseyNumber_pos]

theorem ramseyNumber_eq_one_iff : ((∃ c, n c = 1) ∧ ∀ c, n c ≠ 0) ↔ ramseyNumber n = 1 := by
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ramseyNumber_eq_one h₁ h₂
  intro h
  have : ramseyNumber n ≠ 0 := by rw [h]; simp
  rw [Ne.eq_def, ramseyNumber.eq_zero_iff, not_exists] at this
  obtain ⟨k, hk⟩ := exists_le_one_of_ramseyNumber_le_one h.le
  refine ⟨⟨k, hk.antisymm ?_⟩, this⟩
  rw [Nat.succ_le_iff, pos_iff_ne_zero]
  exact this _

theorem ramseyNumber_unique_colour [Unique K] : ramseyNumber n = n default :=
  by
  refine le_antisymm (ramseyNumber_min_fin (isRamseyValid_unique (by simp))) ?_
  refine ramseyNumber_ge_min _ fun k => ?_
  rw [Subsingleton.elim default k]

@[simp]
theorem ramseyNumber_singleton {i : ℕ} : ramseyNumber ![i] = i := by
  rw [ramseyNumber_unique_colour, Matrix.cons_val_fin_one]

theorem ramseyNumber.mono {n n' : K → ℕ} (h : n ≤ n') : ramseyNumber n ≤ ramseyNumber n' := by
  rw [ramseyNumber_le_iff_fin]; exact (ramseyNumber_spec_fin _).mono_right h

theorem ramseyNumber.mono_two {a b c d : ℕ} (hab : a ≤ b) (hcd : c ≤ d) :
    ramseyNumber ![a, c] ≤ ramseyNumber ![b, d] :=
  ramseyNumber.mono (by rw [Pi.le_def, Fin.forall_fin_two]; exact ⟨hab, hcd⟩)

theorem ramseyNumber_monotone {i : ℕ} : Monotone (ramseyNumber : (Fin i → ℕ) → ℕ) := fun _ _ h =>
  ramseyNumber.mono h

theorem ramseyNumber_remove_two {n : K → ℕ} {n' : K' → ℕ} (f : K' → K)
    (hf : ∀ x : K', n' x ≠ 2 → n (f x) ≠ 2)
    (hf_inj : ∀ x y : K', n' x ≠ 2 → n' y ≠ 2 → f x = f y → x = y)
    (hf_surj : ∀ x : K, n x ≠ 2 → ∃ y : K', n' y ≠ 2 ∧ f y = x)
    (hf_comm : ∀ x : K', n' x ≠ 2 → n (f x) = n' x) : ramseyNumber n' = ramseyNumber n :=
  ramseyNumber_congr fun _ => isRamseyValid_two f hf hf_inj hf_surj hf_comm

@[simp]
theorem ramseyNumber_cons_two {i : ℕ} {n : Fin i → ℕ} :
    ramseyNumber (Matrix.vecCons 2 n) = ramseyNumber n := by
  refine (ramseyNumber_remove_two Fin.succ ?_ ?_ ?_ ?_).symm <;> simp [Fin.forall_fin_succ]

@[simp]
theorem ramseyNumber_cons_zero {i : ℕ} {n : Fin i → ℕ} : ramseyNumber (Matrix.vecCons 0 n) = 0 :=
  ramseyNumber_exists_zero 0 (by simp)

theorem ramseyNumber_cons_one_of_one_le {i : ℕ} {n : Fin i → ℕ} (h : ∀ k, n k ≠ 0) :
    ramseyNumber (Matrix.vecCons 1 n) = 1 :=
  by
  refine ramseyNumber_eq_one ⟨0, rfl⟩ ?_
  rw [Fin.forall_fin_succ]
  simpa using h

theorem ramseyNumber_one_succ {i : ℕ} : ramseyNumber ![1, i + 1] = 1 :=
  ramseyNumber_cons_one_of_one_le (by simp)

theorem ramseyNumber_succ_one {i : ℕ} : ramseyNumber ![i + 1, 1] = 1 := by
  rw [ramseyNumber_pair_swap, ramseyNumber_one_succ]

theorem ramseyNumber_two_left {i : ℕ} : ramseyNumber ![2, i] = i := by simp

@[simp]
theorem ramseyNumber_two_right {i : ℕ} : ramseyNumber ![i, 2] = i := by
  rw [ramseyNumber_pair_swap, ramseyNumber_two_left]

-- if the condition `h` fails, we find a stronger bound from previous results
-- cf `ramsey_number_le_one`
theorem ramseyNumber_multicolour_bound (h : ∀ k, 2 ≤ n k) :
    ramseyNumber n ≤ ∑ k, ramseyNumber (Function.update n k (n k - 1)) + 2 - card K :=
  by
  rw [ramseyNumber_le_iff_fin]
  exact ramsey_fin_induct' _ _ h fun k => ramseyNumber_spec_fin _

-- if the conditions `hi` or `hj` fail, we find a stronger bound from previous results
-- cf `ramsey_number_le_one`
theorem ramseyNumber_two_colour_bound_aux {i j : ℕ} (hi : 2 ≤ i) (hj : 2 ≤ j) :
    ramseyNumber ![i, j] ≤ ramseyNumber ![i - 1, j] + ramseyNumber ![i, j - 1] :=
  by
  rw [ramseyNumber_le_iff_fin]
  refine ramsey_fin_induct_two hi hj ?_ ?_ <;> exact ramseyNumber_spec_fin _

theorem ramseyNumber_two_colour_bound (i j : ℕ) (hij : i ≠ 1 ∨ j ≠ 1) :
    ramseyNumber ![i, j] ≤ ramseyNumber ![i - 1, j] + ramseyNumber ![i, j - 1] :=
  by
  wlog h : i ≤ j generalizing i j
  · refine (ramseyNumber_pair_swap _ _).trans_le ((this _ _ hij.symm (le_of_not_ge h)).trans ?_)
    rw [ramseyNumber_pair_swap, add_comm, add_le_add_iff_right, ramseyNumber_pair_swap]
  rcases i with (_ | _ | i)
  · simp
  · rcases j with (_ | _ | _)
    · simp
    · simp at hij
    rw [ramseyNumber_one_succ, Nat.sub_self, ramseyNumber_cons_zero, zero_add,
      Nat.succ_sub_succ_eq_sub, Nat.sub_zero, ramseyNumber_one_succ]
  have : 2 ≤ i + 2 := by simp
  exact ramseyNumber_two_colour_bound_aux this (this.trans h)

-- a slightly odd shaped bound to make it more practical for explicit computations
theorem ramseyNumber_two_colour_bound_even {i j} (Ni Nj : ℕ) (hi : 2 ≤ i) (hj : 2 ≤ j)
    (hNi : ramseyNumber ![i - 1, j] ≤ Ni) (hNj : ramseyNumber ![i, j - 1] ≤ Nj) (hNi' : Even Ni)
    (hNj' : Even Nj) : ramseyNumber ![i, j] ≤ Ni + Nj - 1 := by
  rw [ramseyNumber_le_iff_fin] at hNi hNj ⊢
  exact ramsey_fin_induct_two_evens hi hj hNi' hNj' hNi hNj

-- if the conditions `hi`, `hj` or `hk` fail, we find a stronger bound from previous results
-- cf `ramsey_number_le_one`
theorem ramseyNumber_three_colour_bound {i j k : ℕ} (hi : 2 ≤ i) (hj : 2 ≤ j) (hk : 2 ≤ k) :
    ramseyNumber ![i, j, k] ≤
      ramseyNumber ![i - 1, j, k] + ramseyNumber ![i, j - 1, k] + ramseyNumber ![i, j, k - 1] - 1 :=
  by
  rw [ramseyNumber_le_iff_fin]
  refine ramsey_fin_induct_three hi hj hk ?_ ?_ ?_ <;> exact ramseyNumber_spec_fin _

/-- The diagonal ramsey number, defined by R(k, k). -/
def diagonalRamsey (k : ℕ) : ℕ :=
  ramseyNumber ![k, k]

theorem diagonalRamsey.def {k : ℕ} : diagonalRamsey k = ramseyNumber ![k, k] :=
  rfl

@[simp]
theorem diagonalRamsey_zero : diagonalRamsey 0 = 0 :=
  ramseyNumber_cons_zero

@[simp]
theorem diagonalRamsey_one : diagonalRamsey 1 = 1 := by
  rw [diagonalRamsey.def, ramseyNumber_one_succ]

@[simp]
theorem diagonalRamsey_two : diagonalRamsey 2 = 2 := by
  rw [diagonalRamsey.def, ramseyNumber_cons_two, ramseyNumber_singleton]

theorem diagonalRamsey_monotone : Monotone diagonalRamsey := fun _ _ hnm =>
  ramseyNumber.mono_two hnm hnm

theorem ramseyNumber_le_choose : ∀ i j : ℕ, ramseyNumber ![i, j] ≤ (i + j - 2).choose (i - 1)
  | 0, _ => by simp
  | _, 0 => by rw [ramseyNumber_pair_swap, ramseyNumber_cons_zero]; exact zero_le'
  | 1, j + 1 => by rw [ramseyNumber_one_succ, Nat.choose_zero_right]
  | i + 1, 1 => by rw [ramseyNumber_succ_one, Nat.succ_sub_succ_eq_sub, Nat.choose_self]
  | i + 2, j + 2 => by
    refine (ramseyNumber_two_colour_bound_aux (Nat.le_add_left _ _) (Nat.le_add_left _ _)).trans ?_
    rw [Nat.add_succ_sub_one, Nat.add_succ_sub_one, ← add_assoc, Nat.add_sub_cancel]
    refine (add_le_add (ramseyNumber_le_choose _ _) (ramseyNumber_le_choose _ _)).trans ?_
    rw [add_add_add_comm, Nat.add_sub_cancel, ← add_assoc, Nat.add_sub_cancel, add_add_add_comm,
      add_right_comm i 2, Nat.choose_succ_succ (i + j + 1) i]
    rfl

theorem diagonalRamsey_le_centralBinom (i : ℕ) : diagonalRamsey i ≤ (i - 1).centralBinom :=
  (ramseyNumber_le_choose i i).trans_eq
    (by rw [Nat.centralBinom_eq_two_mul_choose, Nat.mul_sub_left_distrib, mul_one, two_mul])

theorem diagonalRamsey_le_central_binom' (i : ℕ) : diagonalRamsey i ≤ i.centralBinom :=
  (diagonalRamsey_le_centralBinom _).trans (centralBinom_monotone (Nat.sub_le _ _))

theorem ramseyNumber_pair_le_two_pow {i j : ℕ} : ramseyNumber ![i, j] ≤ 2 ^ (i + j - 2) :=
  (ramseyNumber_le_choose _ _).trans Nat.choose_le_two_pow'

theorem ramseyNumber_pair_le_two_pow' {i j : ℕ} : ramseyNumber ![i, j] ≤ 2 ^ (i + j) :=
  ramseyNumber_pair_le_two_pow.trans (pow_le_pow_right₀ one_le_two (Nat.sub_le _ _))

theorem diagonalRamsey_le_four_pow_sub_one {i : ℕ} : diagonalRamsey i ≤ 4 ^ (i - 1) :=
  ramseyNumber_pair_le_two_pow.trans_eq
    (by rw [show 4 = 2 ^ 2 from rfl, ← pow_mul, Nat.mul_sub_left_distrib, two_mul, mul_one])

theorem diagonalRamsey_le_four_pow {i : ℕ} : diagonalRamsey i ≤ 4 ^ i :=
  diagonalRamsey_le_four_pow_sub_one.trans (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _))

/-- A good bound when i is small and j is large. For `i = 1, 2` this is equality (as long as
`j ≠ 0`), and for `i = 3` and `i = 4` it is the best possible polynomial upper bound, although
lower order improvements are available. -/
theorem ramseyNumber_le_right_pow_left (i j : ℕ) : ramseyNumber ![i, j] ≤ j ^ (i - 1) :=
  by
  rcases Nat.eq_zero_or_pos j with (rfl | hj)
  · rw [ramseyNumber_pair_swap, ramseyNumber_cons_zero]
    exact zero_le'
  refine (ramseyNumber_le_choose i j).trans ?_
  have : i + j - 2 ≤ i - 1 + (j - 1) := add_tsub_add_le_tsub_add_tsub.trans' le_rfl
  -- the way naturals are handled in lean 4 makes me need to change this proof
  refine (Nat.choose_le_choose _ this).trans ?_
  refine (Nat.choose_add_le_pow_left _ _).trans_eq ?_
  rw [Nat.sub_add_cancel hj]

/-- A simplification of `ramsey_number_le_right_pow_left` which is more convenient for asymptotic
reasoning. A good bound when `i` is small and `j` is very large. -/
theorem ramseyNumber_le_right_pow_left' {i j : ℕ} : ramseyNumber ![i, j] ≤ j ^ i :=
  (ramseyNumber_le_right_pow_left (i + 1) j).trans' <| ramseyNumber.mono_two (by simp) le_rfl

end SimpleGraph
