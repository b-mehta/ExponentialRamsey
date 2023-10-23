/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Prereq.Ramsey
import NumberTheory.LegendreSymbol.QuadraticChar.GaussSum
import Prereq.Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

#align_import prereq.ramsey_small

/-!
# Constructions to prove lower bounds on some small Ramsey numbers
-/


namespace SimpleGraph

open Fintype (card)

open Finset

section Paley

variable {F : Type _} [Field F] [Fintype F]

/-- If `F` is a finite field with `|F| = 3 mod 4`, the Paley graph on `F` has an edge `x ~ y` if
`x - y` is a (non-zero) quadratic residue.
The definition should only be used if `card F % 4 ≠ 3`. If this condition fails, the graph should
be directed, but we define it here to just be `⊤` for convenience.
-/
def paleyGraph.{u} (F : Type _) [Field F] [Fintype F] : SimpleGraph F
    where
  Adj x y := x ≠ y ∧ (IsSquare (x - y) ∨ card F % 4 = 3)
  symm := by
    rintro x y ⟨h₁, h₂⟩
    refine' ⟨h₁.symm, _⟩
    rw [or_iff_not_imp_right]
    intro h
    exact symmetric_isSquare h (h₂.resolve_right h)
  loopless _ h := h.1 rfl

theorem paleyGraph_adj' {x y : F} :
    (paleyGraph F).Adj x y ↔ x ≠ y ∧ (IsSquare (x - y) ∨ card F % 4 = 3) :=
  Iff.rfl

instance paleyDecidable [DecidableEq F] : DecidableRel (paleyGraph F).Adj := fun x y =>
  decidable_of_iff' _ paleyGraph_adj'

theorem paleyGraph_adj (hF : card F % 4 ≠ 3) {x y : F} :
    (paleyGraph F).Adj x y ↔ x ≠ y ∧ IsSquare (x - y) :=
  and_congr_right' (or_iff_left hF)

theorem isSquare_sub_of_paleyGraph_adj (hF : card F % 4 ≠ 3) {x y : F}
    (h : (paleyGraph F).Adj x y) : IsSquare (x - y) :=
  ((paleyGraph_adj hF).1 h).2

/-- Addition of `x` is a graph isomorphism of the Paley graph. -/
@[simps]
def rotate (x : F) : paleyGraph F ≃g paleyGraph F
    where
  toEquiv := Equiv.addLeft x
  map_rel_iff' a b := by
    simp only [paley_graph_adj', Equiv.coe_addLeft, Ne.def, add_right_inj, add_sub_add_left_eq_sub]

/-- The graph automorphism rescaling the Paley graph by a non-zero square. -/
@[simps]
def rescale (x : F) (hx : IsSquare x) (hx' : x ≠ 0) : paleyGraph F ≃g paleyGraph F
    where
  toEquiv := (Units.mk0 x hx').mulLeft
  map_rel_iff' := by
    intro a b
    simp only [paley_graph]
    simp (config := { contextual := true }) only [hx', Units.mulLeft_apply, Units.val_mk0, Ne.def,
      mul_eq_mul_left_iff, or_false_iff, not_and, and_congr_right_iff, not_false_iff,
      forall_true_left]
    intro h
    have : a - b ≠ 0 := by rwa [sub_ne_zero]
    refine' or_congr_left _
    haveI : DecidableEq F := Classical.decEq F
    rw [← quadraticChar_one_iff_isSquare hx'] at hx 
    rw [← not_iff_not, ← mul_sub, ← quadraticChar_neg_one_iff_not_isSquare, map_mul, hx, one_mul,
      quadraticChar_neg_one_iff_not_isSquare]

/-- The graph isomorphism witnessing that the Paley graph is self complementary: rescaling by a
non-square.
-/
@[simps]
def selfCompl (hF : card F % 4 ≠ 3) (x : F) (hx : ¬IsSquare x) : paleyGraph Fᶜ ≃g paleyGraph F :=
  have hx' : x ≠ 0 := fun h => hx (h.symm ▸ isSquare_zero F)
  { toEquiv := (Units.mk0 x hx').mulLeft
    map_rel_iff' := by
      intro a b
      rw [paley_graph_adj hF, compl_adj, paley_graph_adj hF]
      simp (config := { contextual := true }) only [hx', Units.mulLeft_apply, Units.val_mk0, Ne.def,
        mul_eq_mul_left_iff, or_false_iff, not_and, and_congr_right_iff, not_false_iff,
        forall_true_left]
      intro h
      have : a - b ≠ 0 := by rwa [sub_ne_zero]
      classical
      rw [← quadraticChar_neg_one_iff_not_isSquare] at hx 
      rw [iff_not_comm, ← mul_sub, ← quadraticChar_neg_one_iff_not_isSquare, map_mul, hx, ←
        quadraticChar_one_iff_isSquare this, neg_mul, one_mul, neg_inj] }

/-- The Paley graph on a finite field `F` viewed as a labelling of edges. -/
def paleyLabelling (F : Type _) [Field F] [Fintype F] [DecidableEq F] :
    TopEdgeLabelling F (Fin 2) :=
  toEdgeLabelling (paleyGraph F)

-- smaller `k` don't need the paley construction
/--
If |F| is 1 mod 4, and the paley labelling contans a monochromatic subset of size k + 2, then `F`
contains a subset of size k not containing 0 or 1, all of whose elements are squares and one more
than squares; and all pairwise differences are square.
For small `k` and `|F|`, this reduction is enough to brute-force check that such a configuration
can be avoided.
-/
theorem no_paley_mono_set [DecidableEq F] {k : ℕ} (hF : card F % 4 = 1)
    (h : ∃ (m : Finset F) (c : _), (paleyLabelling F).MonochromaticOf m c ∧ k + 2 = m.card) :
    ∃ m : Finset F,
      m.card = k ∧
        (0 : F) ∉ m ∧
          (1 : F) ∉ m ∧
            (∀ x ∈ m, IsSquare x) ∧
              (∀ x ∈ m, IsSquare (x - 1 : F)) ∧ (m : Set F).Pairwise fun x y => IsSquare (y - x) :=
  by
  have card_not_three_mod_four : card F % 4 ≠ 3 := by rw [hF];
    simp only [Ne.def, Nat.one_eq_bit1, Nat.one_ne_zero, not_false_iff]
  have card_one_mod_two : card F % 2 = 1 := by
    rw [← Nat.mod_mod_of_dvd (card F) (show 2 ∣ 4 by norm_num), hF, Nat.one_mod]
  have : ∃ x : F, ¬IsSquare x := by
    apply FiniteField.exists_nonsquare
    rwa [Ne.def, FiniteField.even_card_iff_char_two, Nat.mod_two_ne_zero]
  rw [exists_comm] at h 
  simp only [is_ramsey_valid_iff_embedding_aux] at h 
  rw [Fin.exists_fin_two, paley_labelling, to_edge_labelling_label_graph,
    to_edge_labelling_label_graph_compl] at h 
  have : Nonempty ((⊤ : SimpleGraph (Fin (k + 2))) ↪g paley_graph F) :=
    by
    rcases h with (⟨⟨h⟩⟩ | h)
    · obtain ⟨x, hx⟩ := this
      exact ⟨h.trans (self_compl card_not_three_mod_four x hx).toRelEmbedding⟩
    exact h
  have : ∃ f : (⊤ : SimpleGraph (Fin (k + 2))) ↪g paley_graph F, f 0 = 0 :=
    by
    obtain ⟨f⟩ := this
    exact ⟨f.trans (rotate (-f 0)).toRelEmbedding, by simp⟩
  have : ∃ f : (⊤ : SimpleGraph (Fin (k + 2))) ↪g paley_graph F, f 0 = 0 ∧ f 1 = 1 :=
    by
    obtain ⟨f, hf⟩ := this
    have hf1 : IsSquare (f 1) :=
      by
      suffices (paley_graph F).Adj (f 1) (f 0)
        by
        rw [paley_graph_adj card_not_three_mod_four, hf, sub_zero] at this 
        exact this.2
      rw [f.map_rel_iff]
      simp only [top_adj, Ne.def, Fin.one_eq_zero_iff, Nat.succ_succ_ne_one, not_false_iff]
    have hf2 : f 1 ≠ 0 := by
      rw [← hf, Ne.def, RelEmbedding.inj]
      simp only [Fin.one_eq_zero_iff, Nat.succ_succ_ne_one, not_false_iff]
    refine' ⟨f.trans (rescale (f 1) hf1 hf2).symm.toRelEmbedding, _⟩
    simp only [hf2, hf, RelIso.toRelEmbedding_eq_coe, embedding.coe_comp, RelIso.coe_coeFn,
      Function.comp_apply, rescale_symm_apply, Units.val_inv_eq_inv_val, Units.val_mk0,
      MulZeroClass.mul_zero, eq_self_iff_true, inv_mul_cancel, Ne.def, not_false_iff, and_self_iff]
  have hss : Symmetric fun x y : F => IsSquare (y - x) :=
    by
    intro x y h
    exact symmetric_isSquare card_not_three_mod_four h
  suffices
    ∃ m : Finset F,
      k = m.card ∧
        (0 : F) ∉ m ∧
          (1 : F) ∉ m ∧
            (insert (0 : F) (insert (1 : F) (m : Set F))).Pairwise fun x y => IsSquare (y - x)
    by
    obtain ⟨m, hm_card, hm₀, hm₁, hm₂⟩ := this
    rw [Set.pairwise_insert_of_symmetric_of_not_mem hss,
      Set.pairwise_insert_of_symmetric_of_not_mem hss] at hm₂ 
    simp only [mem_coe, Set.mem_insert_iff, sub_zero, forall_eq_or_imp, isSquare_one,
      true_and_iff] at hm₂ 
    · exact ⟨m, hm_card.symm, hm₀, hm₁, hm₂.2, hm₂.1.2, hm₂.1.1⟩
    · exact hm₁
    simp only [hm₀, Set.mem_insert_iff, zero_ne_one, mem_coe, or_self_iff, not_false_iff]
  simp only [← coe_insert]
  obtain ⟨f, hf₀, hf₁⟩ := this
  have : ({0, 1} : Finset F) ⊆ Finset.map f.to_embedding univ :=
    by
    rw [insert_subset, singleton_subset_iff, ← hf₀, ← hf₁]
    exact ⟨mem_map_of_mem _ (by simp), mem_map_of_mem _ (by simp)⟩
  refine' ⟨(univ : Finset (Fin (k + 2))).map f.to_embedding \ {0, 1}, _, _, _, _⟩
  · rw [card_sdiff, card_map, card_doubleton, card_fin, Nat.add_sub_cancel]
    · simp only [Ne.def, zero_ne_one, not_false_iff]
    exact this
  ·
    simp only [mem_sdiff, mem_insert, eq_self_iff_true, mem_singleton, zero_ne_one, or_false_iff,
      not_true, and_false_iff, not_false_iff]
  ·
    simp only [mem_sdiff, mem_insert, one_ne_zero, mem_singleton, eq_self_iff_true, false_or_iff,
      not_true, and_false_iff, not_false_iff]
  rw [insert_eq, insert_eq, ← union_assoc, ← insert_eq, union_comm, sdiff_union_of_subset this]
  simp only [Set.Pairwise, mem_coe, mem_map, exists_prop, mem_univ, true_and_iff,
    forall_exists_index, Ne.def, RelEmbedding.coe_toEmbedding, forall_apply_eq_imp_iff,
    RelEmbedding.inj]
  intro x y h
  exact is_square_sub_of_paley_graph_adj card_not_three_mod_four (f.map_rel_iff.2 (Ne.symm h))

theorem paley_five_bound : ¬IsRamseyValid (ZMod 5) ![3, 3] :=
  by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  classical
  rw [is_ramsey_valid_iff_eq]
  intro h
  specialize h (paley_labelling (ZMod 5))
  have :
    ∃ (m : Finset (ZMod 5)) (c : Fin 2),
      (paley_labelling (ZMod 5)).MonochromaticOf m c ∧ 3 = m.card :=
    by simpa only [Fin.exists_fin_two] using h
  have := no_paley_mono_set (by norm_num) this
  simp only [card_eq_one, ← exists_and_right, @exists_comm (Finset (ZMod 5)), exists_eq_left,
    mem_singleton, forall_eq, coe_singleton, Set.pairwise_singleton, and_true_iff] at this 
  revert this
  decide

theorem paley_seventeen_helper :
    ∀ a : ZMod 17, a ≠ 0 → a ≠ 1 → IsSquare a → IsSquare (a - 1) → a = 2 ∨ a = 9 ∨ a = 16 := by
  decide

-- No pair from {2, 9, 16} has difference a square.
theorem paley_seventeen_bound : ¬IsRamseyValid (ZMod 17) ![4, 4] :=
  by
  haveI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  classical
  rw [is_ramsey_valid_iff_eq]
  intro h
  specialize h (paley_labelling (ZMod 17))
  have :
    ∃ (m : Finset (ZMod 17)) (c : Fin 2),
      (paley_labelling (ZMod 17)).MonochromaticOf m c ∧ 4 = m.card :=
    by simpa only [Fin.exists_fin_two] using h
  have := no_paley_mono_set (by norm_num) this
  simp only [card_eq_two, ← exists_and_right, and_assoc', Ne.def, exists_eq_left, mem_insert,
    @exists_comm (Finset (ZMod 17)), exists_and_left, mem_singleton, forall_eq_or_imp, forall_eq,
    coe_pair, not_or, @eq_comm (ZMod 17) 0, @eq_comm (ZMod 17) 1] at this 
  obtain ⟨a, b, hab, ha₀, hb₀, ha₁, hb₁, ha, hb, ha₁', hb₁', h⟩ := this
  rw [Set.pairwise_insert_of_symmetric_of_not_mem] at h 
  rotate_left
  · intro x y h
    exact symmetric_isSquare (by norm_num) h
  · exact hab
  simp only [Set.pairwise_singleton, Set.mem_singleton_iff, forall_eq, true_and_iff] at h 
  have : a = 2 ∨ a = 9 ∨ a = 16 := paley_seventeen_helper a ha₀ ha₁ ha ha₁'
  have : b = 2 ∨ b = 9 ∨ b = 16 := paley_seventeen_helper b hb₀ hb₁ hb hb₁'
  clear ha₀ ha₁ ha ha₁' hb₀ hb₁ hb hb₁'
  revert h hab
  revert a b
  decide

end Paley

theorem ramseyNumber_three_three : ramseyNumber ![3, 3] = 6 :=
  by
  refine' le_antisymm _ _
  · exact (ramsey_number_two_colour_bound 3 3 (by norm_num)).trans_eq (by simp)
  rw [← not_lt, Nat.lt_succ_iff, ← ZMod.card 5, ramsey_number_le_iff]
  exact paley_five_bound

theorem diagonalRamsey_three : diagonalRamsey 3 = 6 :=
  ramseyNumber_three_three

theorem ramseyNumber_three_four_upper : ramseyNumber ![3, 4] ≤ 9 :=
  by
  refine' (ramsey_number_two_colour_bound_even 4 6 _ _ _ _ _ _).trans_eq _
  · norm_num
  · norm_num
  · norm_num
  · rw [Nat.succ_sub_succ_eq_sub, tsub_zero, ← diagonal_ramsey, diagonal_ramsey_three]
  · norm_num
  · norm_num
  · norm_num

theorem ramseyNumber_four_four : ramseyNumber ![4, 4] = 18 :=
  by
  refine' le_antisymm _ _
  · refine' (ramsey_number_two_colour_bound 4 4 (by norm_num)).trans _
    simp only [Nat.succ_sub_succ_eq_sub, tsub_zero]
    rw [ramsey_number_pair_swap 4]
    linarith [ramsey_number_three_four_upper]
  rw [← not_lt, Nat.lt_succ_iff, ← ZMod.card 17, ramsey_number_le_iff]
  exact paley_seventeen_bound

theorem diagonalRamsey_four : diagonalRamsey 4 = 18 :=
  ramseyNumber_four_four

theorem ramseyNumber_three_four : ramseyNumber ![3, 4] = 9 :=
  by
  refine' eq_of_le_of_not_lt ramsey_number_three_four_upper _
  intro h
  have : diagonal_ramsey 4 ≤ 16 :=
    by
    refine' (ramsey_number_two_colour_bound 4 4 (by norm_num)).trans _
    simp only [Nat.succ_sub_succ_eq_sub, tsub_zero]
    rw [ramsey_number_pair_swap 4]
    linarith only [h]
  rw [diagonal_ramsey_four] at this 
  norm_num at this 

section

/--
A triple of vectors in F₂ ^ 4, which encodes the data of the clebsch colouring in a convenient and
compact way.
For our purposes, it is enough to show that the colouring this induces, `clebsch_colouring`, does
not contain a monochromatic triangle
-/
def parts : Fin 3 → Finset (Fin 4 → ZMod 2) :=
  ![{![1, 1, 0, 0], ![0, 0, 1, 1], ![1, 0, 0, 1], ![1, 1, 1, 0], ![1, 0, 0, 0]},
    {![1, 0, 1, 0], ![0, 1, 0, 1], ![0, 1, 1, 0], ![1, 1, 0, 1], ![0, 1, 0, 0]},
    {![0, 0, 0, 1], ![0, 0, 1, 0], ![0, 1, 1, 1], ![1, 0, 1, 1], ![1, 1, 1, 1]}]

/- ./././Mathport/Syntax/Translate/Basic.lean:641:2: warning: expanding binder collection (x y «expr ∈ » parts[simple_graph.parts] i) -/
theorem parts_property :
    ∀ i : Fin 3, ∀ (x) (_ : x ∈ parts i) (y) (_ : y ∈ parts i), x + y ∉ parts i := by decide

theorem parts_cover : ∀ i : Fin 4 → ZMod 2, i ≠ 0 → ∃ j, i ∈ parts j := by decide

theorem parts_disjoint :
    ∀ (i : Fin 4 → ZMod 2) (j : Fin 3), i ∈ parts j → ∀ k : Fin 3, i ∈ parts k → j = k := by decide

theorem parts_get_aux :
    ∀ i : Fin 4 → ZMod 2, i ≠ 0 → ∃! j, j ∈ (univ : Finset (Fin 3)) ∧ i ∈ parts j :=
  by
  intro i hi
  obtain ⟨j, hj⟩ := parts_cover i hi
  exact ⟨j, ⟨mem_univ _, hj⟩, fun k hk => parts_disjoint _ _ hk.2 _ hj⟩

theorem parts_pair_get_aux :
    ∀ i j : Fin 4 → ZMod 2, i ≠ j → ∃! k, k ∈ (univ : Finset (Fin 3)) ∧ i - j ∈ parts k :=
  fun i j hij => parts_get_aux _ (sub_ne_zero_of_ne hij)

/-- given two distinct vertices in F₂ ^ 4, get the label it should have in the clebsch colouring. -/
def partsPairGet (i j : Fin 4 → ZMod 2) (hij : i ≠ j) : Fin 3 :=
  Finset.choose _ _ (parts_pair_get_aux i j hij)

theorem partsPairGet_spec {i j : Fin 4 → ZMod 2} (hij : i ≠ j) :
    i - j ∈ parts (partsPairGet i j hij) :=
  Finset.choose_property _ _ (parts_pair_get_aux i j hij)

theorem partsPairGet_spec' {i j : Fin 4 → ZMod 2} {c : Fin 3} {hij : i ≠ j}
    (h : partsPairGet i j hij = c) : i + j ∈ parts c := by rw [← h, ← CharTwo.sub_eq_add];
  exact parts_pair_get_spec _

theorem partsPairGet_symm (i j : Fin 4 → ZMod 2) (hij : i ≠ j) :
    partsPairGet j i hij.symm = partsPairGet i j hij :=
  by
  have : i - j = j - i := by rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add, add_comm]
  refine' parts_disjoint (j - i) _ (parts_pair_get_spec hij.symm) _ _
  rw [← this]
  exact parts_pair_get_spec hij

open TopEdgeLabelling

/-- an explicit definition of the clebsch colouring
TODO: find the source I used for this
-/
def clebschColouring : TopEdgeLabelling (Fin 4 → ZMod 2) (Fin 3) :=
  TopEdgeLabelling.mk partsPairGet partsPairGet_symm

theorem clebsch_bound : ¬IsRamseyValid (Fin 4 → ZMod 2) ![3, 3, 3] :=
  by
  rw [is_ramsey_valid_iff_eq]
  push_neg
  refine' ⟨clebsch_colouring, _⟩
  rintro m c hm hc
  have : m.card = 3 := by
    clear hm
    revert c
    simp only [Fin.forall_fin_succ, Fin.forall_fin_two, Matrix.cons_val_zero, Fin.succ_zero_eq_one,
      Matrix.cons_val_one, Matrix.head_cons, Fin.succ_one_eq_two, and_self_iff, eq_comm, imp_self,
      Matrix.cons_vec_bit0_eq_alt0, Matrix.cons_vecAppend, Matrix.empty_vecAppend,
      Matrix.cons_vecAlt0]
  clear hc
  rw [card_eq_three] at this 
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := this
  have hxyz : x ∉ ({y, z} : Set (Fin 4 → ZMod 2)) := by simp [hxy, hxz]
  have hyz' : y ∉ ({z} : Set (Fin 4 → ZMod 2)) := by simp [hyz]
  simp only [coe_insert, coe_pair, monochromatic_of_insert hxyz, monochromatic_of_insert hyz',
    Set.mem_singleton_iff, Set.mem_insert_iff, monochromatic_of_singleton, true_and_iff,
    clebsch_colouring, mk_get] at hm 
  have hyz'' := parts_pair_get_spec' (hm.1 _ rfl)
  have hxy'' := parts_pair_get_spec' (hm.2 _ (Or.inl rfl))
  have hxz'' := parts_pair_get_spec' (hm.2 _ (Or.inr rfl))
  apply parts_property _ _ hxz'' _ hyz''
  rwa [← CharTwo.sub_eq_add, add_sub_add_right_eq_sub, CharTwo.sub_eq_add]

end

theorem ramseyNumber_three_three_three : ramseyNumber ![3, 3, 3] = 17 :=
  by
  refine' le_antisymm _ _
  · refine'
      (ramsey_number_three_colour_bound (Nat.le_succ _) (Nat.le_succ _) (Nat.le_succ _)).trans _
    rw [Nat.succ_sub_succ_eq_sub, tsub_zero, ramsey_number_first_swap 3]
    have : ramsey_number ![3, 3, 2] = ramsey_number ![2, 3, 3] :=
      by
      have : ![2, 3, 3] ∘ ⇑(finRotate 3) = ![3, 3, 2] := by decide
      rw [← this, ramsey_number_equiv]
    rw [this, ramsey_number_cons_two, ← diagonal_ramsey, diagonal_ramsey_three]
  rw [← not_lt, Nat.lt_succ_iff]
  have := clebsch_bound
  rw [← ramsey_number_le_iff, Fintype.card_fun, ZMod.card, Fintype.card_fin] at this 
  exact this

end SimpleGraph

