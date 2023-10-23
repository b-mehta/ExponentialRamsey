/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Prereq.Ramsey
import Prereq.GraphProbability
import Combinatorics.SimpleGraph.Density
import Data.Seq.Seq

#align_import basic

/-!
# Book algorithm

Define the book algorithm with its prerequisites.
-/


open Finset Real

namespace SimpleGraph

open scoped BigOperators

variable {V K : Type*}

theorem cast_card_sdiff {α R : Type*} [AddGroupWithOne R] [DecidableEq α] {s t : Finset α}
    (h : s ⊆ t) : ((t \ s).card : R) = t.card - s.card := by
  rw [card_sdiff h, Nat.cast_sub (card_le_of_subset h)]

/-- For `χ` a labelling and vertex sets `X` `Y` and a label `k`, give the edge density of
`k`-labelled edges between `X` and `Y`. -/
def colDensity [DecidableEq V] [DecidableEq K] (χ : TopEdgeLabelling V K) (k : K) (X Y : Finset V) :
    ℝ :=
  edgeDensity (χ.labelGraph k) X Y

theorem colDensity_comm [DecidableEq V] [DecidableEq K] (χ : TopEdgeLabelling V K) (k : K)
    (X Y : Finset V) : colDensity χ k X Y = colDensity χ k Y X := by
  rw [col_density, edge_density_comm, col_density]

theorem colDensity_nonneg [DecidableEq V] [DecidableEq K] {χ : TopEdgeLabelling V K} {k : K}
    {X Y : Finset V} : 0 ≤ colDensity χ k X Y :=
  Rat.cast_nonneg.2 (edgeDensity_nonneg _ _ _)

theorem colDensity_le_one [DecidableEq V] [DecidableEq K] {χ : TopEdgeLabelling V K} {k : K}
    {X Y : Finset V} : colDensity χ k X Y ≤ 1 :=
  by
  rw [← Rat.cast_one]
  exact Rat.cast_le.2 (edge_density_le_one _ _ _)

theorem colDensity_empty_left [DecidableEq V] [DecidableEq K] {χ : TopEdgeLabelling V K} {k : K}
    {Y : Finset V} : colDensity χ k ∅ Y = 0 := by
  rw [col_density, edge_density_empty_left, Rat.cast_zero]

theorem colDensity_empty_right [DecidableEq V] [DecidableEq K] {χ : TopEdgeLabelling V K} {k : K}
    {X : Finset V} : colDensity χ k X ∅ = 0 := by
  rw [col_density, edge_density_empty_right, Rat.cast_zero]

scoped[ExponentialRamsey] notation "red_density" χ:1024 => SimpleGraph.colDensity χ 0

scoped[ExponentialRamsey] notation "blue_density" χ:1024 => SimpleGraph.colDensity χ 1

/-- the set of neighbours of x which are connected to it by edges labelled k -/
def colNeighbors [Fintype V] [DecidableEq V] [DecidableEq K] (χ : TopEdgeLabelling V K) (k : K)
    (x : V) : Finset V :=
  neighborFinset (χ.labelGraph k) x

scoped[ExponentialRamsey] notation "red_neighbors" χ:1024 => SimpleGraph.colNeighbors χ 0

scoped[ExponentialRamsey] notation "blue_neighbors" χ:1024 => SimpleGraph.colNeighbors χ 1

open scoped ExponentialRamsey

variable [DecidableEq V]

section

variable [Fintype V]

theorem mem_colNeighbors [DecidableEq K] {χ : TopEdgeLabelling V K} {x y : V} {k : K} :
    y ∈ colNeighbors χ k x ↔ ∃ H : x ≠ y, χ.get x y = k := by
  rw [col_neighbors, mem_neighborFinset, TopEdgeLabelling.labelGraph_adj]

theorem mem_col_neighbors' [DecidableEq K] {χ : TopEdgeLabelling V K} {x y : V} {k : K} :
    y ∈ colNeighbors χ k x ↔ ∃ H : y ≠ x, χ.get y x = k := by
  rw [col_neighbors, mem_neighborFinset, adj_comm, TopEdgeLabelling.labelGraph_adj]

theorem mem_colNeighbors_comm [DecidableEq K] {χ : TopEdgeLabelling V K} {x y : V} {k : K} :
    y ∈ colNeighbors χ k x ↔ x ∈ colNeighbors χ k y := by rw [mem_col_neighbors, mem_col_neighbors']

theorem not_mem_colNeighbors [DecidableEq K] {χ : TopEdgeLabelling V K} {x : V} {k : K} :
    x ∉ colNeighbors χ k x :=
  not_mem_neighborFinset_self _ _

end

theorem interedges_card_eq_sum {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {A B : Finset V} :
    (G.interedges A B).card = ∑ x in A, (G.neighborFinset x ∩ B).card :=
  by
  have : ∀ e ∈ G.interedges A B, Prod.fst e ∈ A :=
    by
    rintro ⟨e₁, e₂⟩ h
    rw [interedges, Rel.mk_mem_interedges_iff] at h
    exact h.1
  rw [card_eq_sum_card_fiberwise this]
  refine' sum_congr rfl _
  intro x hx
  rw [interedges, Rel.interedges, filter_filter]
  simp only [and_comm']
  rw [← filter_filter, filter_product_left fun i => i = x, Finset.filter_eq', if_pos hx,
    singleton_product, filter_map, card_map, inter_comm, ← filter_mem_eq_inter]
  congr 1
  refine' filter_congr _
  simp only [Function.Embedding.coeFn_mk, mem_neighborFinset, iff_self_iff, imp_true_iff]

theorem colDensity_eq_sum {K : Type*} [Fintype V] [DecidableEq K] {χ : TopEdgeLabelling V K}
    {k : K} {A B : Finset V} :
    colDensity χ k A B = (∑ x in A, (colNeighbors χ k x ∩ B).card) / (A.card * B.card) :=
  by
  rw [col_density, edge_density_def, interedges_card_eq_sum]
  simp only [Nat.cast_sum, Rat.cast_div, Rat.cast_sum, Rat.cast_coe_nat, Rat.cast_mul]
  rfl

section

variable [Fintype V]

/-- Define the weight of an ordered pair for the book algorithm.
`pair_weight χ X Y x y` corresponds to `ω(x, y)` in the paper, see equation (3).
-/
noncomputable def pairWeight (χ : TopEdgeLabelling V (Fin 2)) (X Y : Finset V) (x y : V) : ℝ :=
  Y.card⁻¹ *
    (((red_neighbors χ) x ∩ (red_neighbors χ) y ∩ Y).card -
      (red_density χ) X Y * ((red_neighbors χ) x ∩ Y).card)

/-- Define the weight of a vertex for the book algorithm.
`pair_weight χ X Y x` corresponds to `ω(x)` in the paper, see equation (4).
-/
noncomputable def weight (χ : TopEdgeLabelling V (Fin 2)) (X Y : Finset V) (x : V) : ℝ :=
  ∑ y in X.eraseₓ x, pairWeight χ X Y x y

end

/-- Define the function `q` from the paper, see equation (5).  -/
noncomputable def qFunction (k : ℕ) (p₀ : ℝ) (h : ℕ) : ℝ :=
  p₀ + ((1 + k ^ (-1 / 4 : ℝ)) ^ h - 1) / k

theorem qFunction_zero {k : ℕ} {p₀ : ℝ} : qFunction k p₀ 0 = p₀ := by
  rw [q_function, pow_zero, sub_self, zero_div, add_zero]

theorem qFunction_one {k : ℕ} {p₀ : ℝ} : qFunction k p₀ 1 = p₀ + k ^ (-1 / 4 : ℝ) / k := by
  rw [q_function, pow_one, add_sub_cancel']

theorem q_increasing {k h₁ h₂ : ℕ} {p₀ : ℝ} (h : h₁ ≤ h₂) : qFunction k p₀ h₁ ≤ qFunction k p₀ h₂ :=
  by
  rw [q_function, q_function, add_le_add_iff_left]
  refine' div_le_div_of_le (Nat.cast_nonneg _) (sub_le_sub_right (pow_le_pow _ h) _)
  rw [le_add_iff_nonneg_right]
  exact rpow_nonneg_of_nonneg (Nat.cast_nonneg _) _

theorem qFunction_weak_lower {k : ℕ} {p₀ : ℝ} {h : ℕ} :
    p₀ + h * k ^ (-1 / 4 : ℝ) / k ≤ qFunction k p₀ h :=
  by
  rw [q_function, add_le_add_iff_left]
  refine' div_le_div_of_le (Nat.cast_nonneg _) _
  refine' (sub_le_sub_right (one_add_mul_le_pow _ h) _).trans_eq' _
  · exact (rpow_nonneg_of_nonneg (Nat.cast_nonneg _) _).trans' (by norm_num)
  rw [add_sub_cancel']

-- The bound on h here is about k / ε, which is not good enough in general so I'm not gonna bother
-- exposing it, later I show h ≤ 2 log k / ε works for suff large k, which is what's actually needed
theorem qFunction_above (p₀ c : ℝ) {k : ℕ} (hk : k ≠ 0) : ∃ h, 1 ≤ h ∧ c ≤ qFunction k p₀ h :=
  by
  refine' ⟨max 1 ⌈(c - p₀) * k / k ^ (-1 / 4 : ℝ)⌉₊, le_max_left _ _, _⟩
  refine' (q_increasing (le_max_right _ _)).trans' _
  refine' q_function_weak_lower.trans' _
  rw [← sub_le_iff_le_add', mul_div_assoc, ← div_le_iff, div_div_eq_mul_div]
  · exact Nat.le_ceil _
  · positivity

/-- Define the height, `h(p)` from the paper. See equation (5). -/
noncomputable def height (k : ℕ) (p₀ p : ℝ) : ℕ :=
  if h : k ≠ 0 then Nat.find (qFunction_above p₀ p h) else 1

theorem one_le_height {k : ℕ} {p₀ p : ℝ} : 1 ≤ height k p₀ p :=
  by
  rw [height]
  split_ifs with h
  · exact (Nat.find_spec (q_function_above p₀ p h)).1
  exact le_rfl

/-- Define function `α_h` from the paper. We use the right half of equation (6) as the definition
for simplicity, and `α_function_eq_q_diff` gives the left half. -/
noncomputable def αFunction (k : ℕ) (h : ℕ) : ℝ :=
  k ^ (-1 / 4 : ℝ) * (1 + k ^ (-1 / 4 : ℝ)) ^ (h - 1) / k

theorem αFunction_eq_q_diff {k : ℕ} {p₀ : ℝ} {h : ℕ} :
    αFunction k (h + 1) = qFunction k p₀ (h + 1) - qFunction k p₀ h := by
  rw [α_function, q_function, q_function, add_sub_add_left_eq_sub, div_sub_div_same,
    sub_sub_sub_cancel_right, pow_succ, ← sub_one_mul, add_sub_cancel', Nat.add_sub_cancel]

variable {χ : TopEdgeLabelling V (Fin 2)}

open TopEdgeLabelling

/-- the quadruple of sets X,Y,A,B that we keep track of in the book algorithm, bundled with the
properties which are needed for it
-/
structure BookConfig (χ : TopEdgeLabelling V (Fin 2)) where
  (X y A B : Finset V)
  hXY : Disjoint X Y
  hXA : Disjoint X A
  hXB : Disjoint X B
  hYA : Disjoint Y A
  hYB : Disjoint Y B
  hAB : Disjoint A B
  red_a : χ.MonochromaticOf A 0
  red_XYA : χ.MonochromaticBetween (X ∪ Y) A 0
  blue_b : χ.MonochromaticOf B 1
  blue_XB : χ.MonochromaticBetween X B 1

namespace BookConfig

/-- Define `p` from the paper at a given configuration. -/
def p (C : BookConfig χ) : ℝ :=
  (red_density χ) C.X C.y

section

variable [Fintype V]

/-- Given a vertex set `X`, construct the initial configuration where `X` is as given. -/
def start (X : Finset V) : BookConfig χ :=
  by
  refine' ⟨X, Xᶜ, ∅, ∅, disjoint_compl_right, _, _, _, _, _, _, _, _, _⟩
  all_goals simp

-- todo: this instance shouldn't need fintype; just use everything empty
instance : Inhabited (BookConfig χ) :=
  ⟨start ∅⟩

/-- Take a red step for the book algorithm, given `x ∈ X`. -/
def redStepBasic (C : BookConfig χ) (x : V) (hx : x ∈ C.X) : BookConfig χ
    where
  X := (red_neighbors χ) x ∩ C.X
  y := (red_neighbors χ) x ∩ C.y
  A := insert x C.A
  B := C.B
  hXY := disjoint_of_subset_left (inter_subset_right _ _) (C.hXY.inf_right' _)
  hXA := by
    rw [disjoint_insert_right, mem_inter, not_and_or]
    refine' ⟨Or.inl not_mem_col_neighbors, _⟩
    exact disjoint_of_subset_left (inter_subset_right _ _) C.hXA
  hXB := disjoint_of_subset_left (inter_subset_right _ _) C.hXB
  hYA := by
    rw [disjoint_insert_right, mem_inter, not_and_or]
    refine' ⟨Or.inl not_mem_col_neighbors, _⟩
    exact disjoint_of_subset_left (inter_subset_right _ _) C.hYA
  hYB := disjoint_of_subset_left (inter_subset_right _ _) C.hYB
  hAB := by
    simp only [disjoint_insert_left, C.hAB, and_true_iff]
    exact Finset.disjoint_left.1 C.hXB hx
  red_a := by
    have : x ∉ (C.A : Set V) := Finset.disjoint_left.1 C.hXA hx
    rw [coe_insert, TopEdgeLabelling.MonochromaticOf_insert this, and_iff_right C.red_A]
    intro a ha
    exact C.red_XYA (mem_union_left _ hx) ha _
  red_XYA :=
    by
    rw [← inter_distrib_left, insert_eq, TopEdgeLabelling.monochromatic_between_union_right,
      TopEdgeLabelling.monochromatic_between_singleton_right]
    constructor
    · simp (config := { contextual := true }) [mem_col_neighbors']
    · exact C.red_XYA.subset_left (inter_subset_right _ _)
  blue_b := C.blue_b
  blue_XB := C.blue_XB.subset_left (inter_subset_right _ _)

theorem redStepBasic_x {C : BookConfig χ} {x : V} (hx : x ∈ C.X) :
    (redStepBasic C x hx).X = (red_neighbors χ) x ∩ C.X :=
  rfl

theorem redStepBasic_y {C : BookConfig χ} {x : V} (hx : x ∈ C.X) :
    (redStepBasic C x hx).y = (red_neighbors χ) x ∩ C.y :=
  rfl

theorem redStepBasic_a {C : BookConfig χ} {x : V} (hx : x ∈ C.X) :
    (redStepBasic C x hx).A = insert x C.A :=
  rfl

theorem redStepBasic_b {C : BookConfig χ} {x : V} (hx : x ∈ C.X) : (redStepBasic C x hx).B = C.B :=
  rfl

end

section

/-- Take a big blue step for the book algorithm, given a blue book `(S, T)` contained in `X`. -/
def bigBlueStepBasic (C : BookConfig χ) (S T : Finset V) (hS : S ⊆ C.X) (hT : T ⊆ C.X)
    (hSS : χ.MonochromaticOf S 1) (hST : Disjoint S T) (hST' : χ.MonochromaticBetween S T 1) :
    BookConfig χ where
  X := T
  y := C.y
  A := C.A
  B := C.B ∪ S
  hXY := disjoint_of_subset_left hT C.hXY
  hXA := disjoint_of_subset_left hT C.hXA
  hXB := disjoint_union_right.2 ⟨disjoint_of_subset_left hT C.hXB, hST.symm⟩
  hYA := C.hYA
  hYB := disjoint_union_right.2 ⟨C.hYB, disjoint_of_subset_right hS C.hXY.symm⟩
  hAB := disjoint_union_right.2 ⟨C.hAB, disjoint_of_subset_right hS C.hXA.symm⟩
  red_a := C.red_a
  red_XYA := C.red_XYA.subset_left (union_subset_union hT Subset.rfl)
  blue_b := by
    rw [coe_union, TopEdgeLabelling.MonochromaticOf_union]
    exact ⟨C.blue_B, hSS, C.blue_XB.symm.subset_right hS⟩
  blue_XB := by
    rw [TopEdgeLabelling.monochromatic_between_union_right]
    exact ⟨C.blue_XB.subset_left hT, hST'.symm⟩

variable [Fintype V]

/-- Take a density boost step for the book algorithm, given `x ∈ X`. -/
def densityBoostStepBasic (C : BookConfig χ) (x : V) (hx : x ∈ C.X) : BookConfig χ
    where
  X := (blue_neighbors χ) x ∩ C.X
  y := (red_neighbors χ) x ∩ C.y
  A := C.A
  B := insert x C.B
  hXY := (C.hXY.inf_left' _).inf_right' _
  hXA := C.hXA.inf_left' _
  hXB := by
    rw [disjoint_insert_right, mem_inter, not_and_or]
    exact ⟨Or.inl not_mem_col_neighbors, C.hXB.inf_left' _⟩
  hYA := C.hYA.inf_left' _
  hYB := by
    rw [disjoint_insert_right, mem_inter, not_and_or]
    exact ⟨Or.inl not_mem_col_neighbors, C.hYB.inf_left' _⟩
  hAB := by
    simp only [disjoint_insert_right, C.hAB, and_true_iff]
    exact Finset.disjoint_left.1 C.hXA hx
  red_a := C.red_a
  red_XYA :=
    C.red_XYA.subset_left (union_subset_union (inter_subset_right _ _) (inter_subset_right _ _))
  blue_b := by
    rw [insert_eq, coe_union, MonochromaticOf_union, coe_singleton]
    exact ⟨MonochromaticOf_singleton, C.blue_B, C.blue_XB.subset_left (by simpa using hx)⟩
  blue_XB :=
    by
    rw [insert_eq, monochromatic_between_union_right, monochromatic_between_singleton_right]
    refine' ⟨_, C.blue_XB.subset_left (inter_subset_right _ _)⟩
    simp (config := { contextual := true }) [mem_col_neighbors']

theorem densityBoostStepBasic_x {C : BookConfig χ} {x : V} (hx : x ∈ C.X) :
    (densityBoostStepBasic C x hx).X = (blue_neighbors χ) x ∩ C.X :=
  rfl

theorem densityBoostStepBasic_y {C : BookConfig χ} {x : V} (hx : x ∈ C.X) :
    (densityBoostStepBasic C x hx).y = (red_neighbors χ) x ∩ C.y :=
  rfl

theorem densityBoostStepBasic_a {C : BookConfig χ} {x : V} (hx : x ∈ C.X) :
    (densityBoostStepBasic C x hx).A = C.A :=
  rfl

theorem densityBoostStepBasic_b {C : BookConfig χ} {x : V} (hx : x ∈ C.X) :
    (densityBoostStepBasic C x hx).B = insert x C.B :=
  rfl

end

section

/-- Take a degree regularisation step for the book algorithm, given `U ⊆ X` for the vertices we want
to keep in `X`. -/
def degreeRegularisationStepBasic (C : BookConfig χ) (U : Finset V) (h : U ⊆ C.X) : BookConfig χ
    where
  X := U
  y := C.y
  A := C.A
  B := C.B
  hXY := C.hXY.mono_left h
  hXA := C.hXA.mono_left h
  hXB := C.hXB.mono_left h
  hYA := C.hYA
  hYB := C.hYB
  hAB := C.hAB
  red_a := C.red_a
  red_XYA := C.red_XYA.subset_left (union_subset_union h Subset.rfl)
  blue_b := C.blue_b
  blue_XB := C.blue_XB.subset_left h

variable [Fintype V]

/-- Take a degree regularisation step, choosing the set of vertices as in the paper. -/
noncomputable def degreeRegularisationStep (k : ℕ) (p₀ : ℝ) (C : BookConfig χ) : BookConfig χ :=
  degreeRegularisationStepBasic C
    (C.X.filterₓ fun x =>
      (C.p - k ^ (1 / 8 : ℝ) * αFunction k (height k p₀ C.p)) * C.y.card ≤
        ((red_neighbors χ) x ∩ C.y).card)
    (filter_subset _ _)

theorem degreeRegularisationStep_x {k : ℕ} {p₀ : ℝ} {C : BookConfig χ} :
    (degreeRegularisationStep k p₀ C).X =
      C.X.filterₓ fun x =>
        (C.p - k ^ (1 / 8 : ℝ) * αFunction k (height k p₀ C.p)) * C.y.card ≤
          ((red_neighbors χ) x ∩ C.y).card :=
  rfl

theorem degreeRegularisationStep_y {k : ℕ} {p₀ : ℝ} {C : BookConfig χ} :
    (degreeRegularisationStep k p₀ C).y = C.y :=
  rfl

theorem degreeRegularisationStep_a {k : ℕ} {p₀ : ℝ} {C : BookConfig χ} :
    (degreeRegularisationStep k p₀ C).A = C.A :=
  rfl

theorem degreeRegularisationStep_b {k : ℕ} {p₀ : ℝ} {C : BookConfig χ} :
    (degreeRegularisationStep k p₀ C).B = C.B :=
  rfl

theorem degreeRegularisationStep_x_subset {k : ℕ} {p₀ : ℝ} {C : BookConfig χ} :
    (degreeRegularisationStep k p₀ C).X ⊆ C.X :=
  filter_subset _ _

end

/-- Get the set of appropriately sized blue books contained in `X`. We will take a maximal
one of these later. -/
noncomputable def usefulBlueBooks {V : Type*} [DecidableEq V] (χ : TopEdgeLabelling V (Fin 2))
    (μ : ℝ) (X : Finset V) : Finset (Finset V × Finset V) :=
  (X.powerset.product X.powerset).filterₓ fun ST =>
    Disjoint ST.1 ST.2 ∧
      χ.MonochromaticOf ST.1 1 ∧
        χ.MonochromaticBetween ST.1 ST.2 1 ∧ μ ^ ST.1.card * X.card / 2 ≤ ST.2.card

theorem mem_usefulBlueBooks {μ : ℝ} {X : Finset V} {ST : Finset V × Finset V} :
    ST ∈ usefulBlueBooks χ μ X ↔
      ST.1 ⊆ X ∧
        ST.2 ⊆ X ∧
          Disjoint ST.1 ST.2 ∧
            χ.MonochromaticOf ST.1 1 ∧
              χ.MonochromaticBetween ST.1 ST.2 1 ∧ μ ^ ST.1.card * X.card / 2 ≤ ST.2.card :=
  by rw [useful_blue_books, mem_filter, mem_product, mem_powerset, mem_powerset, and_assoc']

theorem mem_useful_blue_books' {μ : ℝ} {X S T : Finset V} :
    (S, T) ∈ usefulBlueBooks χ μ X ↔
      S ⊆ X ∧
        T ⊆ X ∧
          Disjoint S T ∧
            χ.MonochromaticOf S 1 ∧
              χ.MonochromaticBetween S T 1 ∧ μ ^ S.card * X.card / 2 ≤ T.card :=
  mem_usefulBlueBooks

theorem exists_useful_blue_book (μ : ℝ) (X : Finset V) : (usefulBlueBooks χ μ X).Nonempty :=
  by
  use(∅, X)
  rw [mem_useful_blue_books']
  simp only [empty_subset, subset.refl, disjoint_empty_left, coe_empty, MonochromaticOf_empty,
    TopEdgeLabelling.monochromatic_between_empty_left, card_empty, pow_zero, one_mul,
    true_and_iff]
  exact half_le_self (Nat.cast_nonneg _)

theorem exists_blue_book_one_le_S [Fintype V] (μ : ℝ) (X : Finset V)
    (hX : ∃ x ∈ X, μ * X.card ≤ ((blue_neighbors χ) x ∩ X).card) :
    ∃ ST : Finset V × Finset V, ST ∈ usefulBlueBooks χ μ X ∧ 1 ≤ ST.1.card :=
  by
  obtain ⟨x, hx, hx'⟩ := hX
  cases lt_or_le μ 0
  · refine' ⟨⟨{x}, ∅⟩, _, by simp⟩
    rw [mem_useful_blue_books']
    simp only [singleton_subset_iff, empty_subset, disjoint_singleton_left, not_mem_empty,
      not_false_iff, coe_singleton, MonochromaticOf_singleton, true_and_iff, hx, Nat.cast_zero,
      TopEdgeLabelling.monochromatic_between_empty_right, card_singleton, pow_one, card_empty]
    refine' div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg h.le _) (by norm_num1)
    positivity
  refine' ⟨⟨{x}, (blue_neighbors χ) x ∩ X⟩, _, by simp⟩
  rw [mem_useful_blue_books']
  simp (config := { contextual := true }) only [hx, singleton_subset_iff, disjoint_singleton_left,
    mem_inter, and_true_iff, coe_singleton, MonochromaticOf_singleton, card_singleton, pow_one,
    true_and_iff, inter_subset_right, not_true, not_mem_col_neighbors,
    TopEdgeLabelling.monochromatic_between_singleton_left, and_imp, mem_col_neighbors, Ne.def,
    eq_self_iff_true, not_false_iff, IsEmpty.exists_iff, forall_exists_index, imp_true_iff]
  refine' hx'.trans' (half_le_self _)
  positivity

theorem exists_maximal_blue_book_aux (χ : TopEdgeLabelling V (Fin 2)) (μ : ℝ) (X : Finset V) :
    ∃ ST ∈ usefulBlueBooks χ μ X,
      ∀ ST' ∈ usefulBlueBooks χ μ X, Finset.card (Prod.fst ST') ≤ Finset.card (Prod.fst ST) :=
  Finset.exists_max_image (usefulBlueBooks χ μ X) (fun ST => ST.1.card)
    (exists_useful_blue_book _ _)

/-- Get a maximal book contained in `X`. -/
noncomputable def getBook (χ : TopEdgeLabelling V (Fin 2)) (μ : ℝ) (X : Finset V) :
    Finset V × Finset V :=
  (exists_maximal_blue_book_aux χ μ X).some

theorem getBook_mem (μ : ℝ) (X : Finset V) : getBook χ μ X ∈ usefulBlueBooks χ μ X :=
  (exists_maximal_blue_book_aux χ μ X).choose_spec.some

theorem getBook_fst_subset {μ : ℝ} {X : Finset V} : (getBook χ μ X).1 ⊆ X :=
  (mem_usefulBlueBooks.1 (getBook_mem μ X)).1

theorem getBook_snd_subset {μ : ℝ} {X : Finset V} : (getBook χ μ X).2 ⊆ X :=
  (mem_usefulBlueBooks.1 (getBook_mem μ X)).2.1

theorem getBook_disjoints {μ : ℝ} {X : Finset V} : Disjoint (getBook χ μ X).1 (getBook χ μ X).2 :=
  (mem_usefulBlueBooks.1 (getBook_mem μ X)).2.2.1

theorem getBook_blue_fst {μ : ℝ} {X : Finset V} : χ.MonochromaticOf (getBook χ μ X).1 1 :=
  (mem_usefulBlueBooks.1 (getBook_mem μ X)).2.2.2.1

theorem getBook_blue_fst_snd {μ : ℝ} {X : Finset V} :
    χ.MonochromaticBetween (getBook χ μ X).1 (getBook χ μ X).2 1 :=
  (mem_usefulBlueBooks.1 (getBook_mem μ X)).2.2.2.2.1

theorem getBook_relative_card {μ : ℝ} {X : Finset V} :
    μ ^ (getBook χ μ X).1.card * X.card / 2 ≤ (getBook χ μ X).2.card :=
  (mem_usefulBlueBooks.1 (getBook_mem μ X)).2.2.2.2.2

theorem getBook_max {μ : ℝ} {X : Finset V} (S T : Finset V) (hST : (S, T) ∈ usefulBlueBooks χ μ X) :
    S.card ≤ (getBook χ μ X).1.card :=
  (exists_maximal_blue_book_aux χ μ X).choose_spec.choose_spec (S, T) hST

section

variable [Fintype V]

theorem one_le_card_getBook_fst {μ : ℝ} {X : Finset V}
    (hX : ∃ x ∈ X, μ * X.card ≤ ((blue_neighbors χ) x ∩ X).card) : 1 ≤ (getBook χ μ X).1.card :=
  by
  obtain ⟨⟨S, T⟩, hST, hS⟩ := exists_blue_book_one_le_S _ _ hX
  exact hS.trans (get_book_max _ _ hST)

theorem getBook_snd_card_le_X {μ : ℝ} {X : Finset V}
    (hX : ∃ x ∈ X, μ * X.card ≤ ((blue_neighbors χ) x ∩ X).card) :
    (getBook χ μ X).2.card + 1 ≤ X.card :=
  by
  refine' (add_le_add_left (one_le_card_get_book_fst hX) _).trans _
  rw [add_comm, ← card_disjoint_union]
  · exact card_le_of_subset (union_subset get_book_fst_subset get_book_snd_subset)
  exact get_book_disjoints

/-- The number of vertices with a large blue neighbourhood. -/
noncomputable def numBigBlues (μ : ℝ) (C : BookConfig χ) : ℕ :=
  (C.X.filterₓ fun x => μ * C.X.card ≤ ((blue_neighbors χ) x ∩ C.X).card).card

theorem get_book_condition {μ : ℝ} {k l : ℕ} {C : BookConfig χ} (hk : k ≠ 0) (hl : l ≠ 0)
    (hX : ramseyNumber ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊] ≤ numBigBlues μ C) :
    ∃ x ∈ C.X, μ * C.X.card ≤ ((blue_neighbors χ) x ∩ C.X).card :=
  by
  rw [← filter_nonempty_iff, ← card_pos]
  refine' hX.trans_lt' _
  rw [ramsey_number_pos]
  rw [Fin.forall_fin_two]
  simp only [Matrix.cons_val_zero, Ne.def, Matrix.cons_val_one, Matrix.head_cons, Nat.ceil_eq_zero,
    not_le, hk, not_false_iff, true_and_iff]
  positivity

end

/-- Perform a big blue step, picking an appropriate blue book. -/
noncomputable def bigBlueStep (μ : ℝ) (C : BookConfig χ) : BookConfig χ :=
  bigBlueStepBasic C (getBook χ μ C.X).1 (getBook χ μ C.X).2 getBook_fst_subset getBook_snd_subset
    getBook_blue_fst getBook_disjoints getBook_blue_fst_snd

theorem bigBlueStep_x {μ : ℝ} {C : BookConfig χ} : (bigBlueStep μ C).X = (getBook χ μ C.X).2 :=
  rfl

theorem bigBlueStep_y {μ : ℝ} {C : BookConfig χ} : (bigBlueStep μ C).y = C.y :=
  rfl

theorem bigBlueStep_a {μ : ℝ} {C : BookConfig χ} : (bigBlueStep μ C).A = C.A :=
  rfl

theorem bigBlueStep_b {μ : ℝ} {C : BookConfig χ} :
    (bigBlueStep μ C).B = C.B ∪ (getBook χ μ C.X).1 :=
  rfl

section

variable [Fintype V]

/-- The set of viable central vertices. -/
noncomputable def centralVertices (μ : ℝ) (C : BookConfig χ) : Finset V :=
  C.X.filterₓ fun x => ↑((blue_neighbors χ) x ∩ C.X).card ≤ μ * C.X.card

theorem exists_central_vertex (μ : ℝ) (C : BookConfig χ)
    (hX : ∃ x ∈ C.X, ↑((blue_neighbors χ) x ∩ C.X).card ≤ μ * C.X.card) :
    ∃ x ∈ centralVertices μ C, ∀ y ∈ centralVertices μ C, weight χ C.X C.y y ≤ weight χ C.X C.y x :=
  exists_max_image _ _ (by rwa [central_vertices, filter_nonempty_iff])

/-- Get the central vertex as in step 3. -/
noncomputable def getCentralVertex (μ : ℝ) (C : BookConfig χ)
    (hX : ∃ x ∈ C.X, ↑((blue_neighbors χ) x ∩ C.X).card ≤ μ * C.X.card) : V :=
  (exists_central_vertex μ C hX).some

theorem getCentralVertex_mem (μ : ℝ) (C : BookConfig χ)
    (hX : ∃ x ∈ C.X, ↑((blue_neighbors χ) x ∩ C.X).card ≤ μ * C.X.card) :
    getCentralVertex μ C hX ∈ centralVertices μ C :=
  (exists_central_vertex μ C hX).choose_spec.some

theorem getCentralVertex_mem_x (μ : ℝ) (C : BookConfig χ)
    (hX : ∃ x ∈ C.X, ↑((blue_neighbors χ) x ∩ C.X).card ≤ μ * C.X.card) :
    getCentralVertex μ C hX ∈ C.X :=
  mem_of_mem_filter _ (getCentralVertex_mem _ _ _)

theorem getCentralVertex_max (μ : ℝ) (C : BookConfig χ)
    (hX : ∃ x ∈ C.X, ↑((blue_neighbors χ) x ∩ C.X).card ≤ μ * C.X.card) (y : V)
    (hy : y ∈ centralVertices μ C) :
    weight χ C.X C.y y ≤ weight χ C.X C.y (getCentralVertex μ C hX) :=
  (exists_central_vertex μ C hX).choose_spec.choose_spec _ hy

theorem get_central_vertex_condition {μ : ℝ} {k l : ℕ} (C : BookConfig χ)
    (h : ¬(C.X.card ≤ ramseyNumber ![k, ⌈(l : ℝ) ^ (3 / 4 : ℝ)⌉₊] ∨ C.p ≤ 1 / k))
    (h' : ¬ramseyNumber ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊] ≤ numBigBlues μ C) :
    ∃ x ∈ C.X, ↑((blue_neighbors χ) x ∩ C.X).card ≤ μ * C.X.card :=
  by
  rw [not_or, not_le] at h
  rw [not_le] at h'
  rw [← filter_nonempty_iff, ← card_pos]
  simp only [← not_lt]
  rw [filter_not, card_sdiff (filter_subset _ _)]
  refine' Nat.sub_pos_of_lt (h.1.trans_le' _)
  refine' ((card_le_of_subset _).trans_lt h').le.trans _
  · exact monotone_filter_right _ fun y hy => hy.le
  refine' ramsey_number.mono_two le_rfl (Nat.ceil_mono _)
  cases l
  · rw [Nat.cast_zero, zero_rpow, zero_rpow] <;> norm_num1
  refine' rpow_le_rpow_of_exponent_le _ (by norm_num1)
  simp

end

end BookConfig

variable [Fintype V]

/-- The book algorithm as an infinite sequence which is eventually constantly nothing. -/
noncomputable def algorithmOption (μ : ℝ) (k l : ℕ) (ini : BookConfig χ) : ℕ → Option (BookConfig χ)
  | 0 => some ini
  | i + 1 =>
    match algorithm_option i with
    | none => none
    | some C =>
      if h : C.X.card ≤ ramseyNumber ![k, ⌈(l : ℝ) ^ (3 / 4 : ℝ)⌉₊] ∨ C.p ≤ 1 / k then none
      else
        some <|
          if Even i then C.degreeRegularisationStep k ini.p
          else
            if h' : ramseyNumber ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊] ≤ C.numBigBlues μ then
              C.bigBlueStep μ
            else
              let x := C.getCentralVertex μ (C.get_central_vertex_condition h h')
              if
                  C.p - αFunction k (height k ini.p C.p) ≤
                    (red_density χ) ((red_neighbors χ) x ∩ C.X) ((red_neighbors χ) x ∩ C.y) then
                C.redStepBasic x (C.getCentralVertex_mem_x _ _)
              else C.densityBoostStepBasic x (C.getCentralVertex_mem_x _ _)

variable {μ : ℝ} {k l : ℕ} {ini : BookConfig χ}

theorem algorithmOption_stays_none {i : ℕ} (hi : algorithmOption μ k l ini i = none) :
    algorithmOption μ k l ini (i + 1) = none :=
  by
  rw [algorithm_option, hi]
  rfl

theorem algorithmOption_is_some_of {i : ℕ} (hi : ∃ C, algorithmOption μ k l ini (i + 1) = some C) :
    ∃ C, algorithmOption μ k l ini i = some C :=
  by
  contrapose! hi
  simp only [Ne.def, ← Option.mem_def, ← Option.eq_none_iff_forall_not_mem] at hi ⊢
  exact algorithm_option_stays_none hi

theorem algorithmOption_x_weak_bound {i : ℕ} (C : BookConfig χ) (hk : k ≠ 0) (hl : l ≠ 0)
    (hC : algorithmOption μ k l ini i = some C) : C.X.card + i / 2 ≤ ini.X.card :=
  by
  induction' i with i ih generalizing C
  · rw [Nat.zero_div, add_zero]
    simp only [algorithm_option] at hC
    rw [← hC]
  obtain ⟨C', hC'⟩ := algorithm_option_is_some_of ⟨C, hC⟩
  rw [algorithm_option, hC', algorithm_option._match_1] at hC
  by_cases h₁ : C'.X.card ≤ ramsey_number ![k, ⌈(l : ℝ) ^ (3 / 4 : ℝ)⌉₊] ∨ C'.p ≤ 1 / k
  · simpa only [dif_pos h₁] using hC
  rw [dif_neg h₁] at hC
  by_cases h₂ : Even i
  · simp only [if_pos h₂] at hC
    rw [even_iff_exists_bit0] at h₂
    obtain ⟨i, rfl⟩ := h₂
    rw [Nat.succ_eq_add_one, ← bit1, Nat.bit1_div_two, ← hC]
    rw [Nat.bit0_div_two] at ih
    exact (ih _ hC').trans' (add_le_add_right (card_le_of_subset (filter_subset _ _)) _)
  rw [if_neg h₂] at hC
  rw [← Nat.odd_iff_not_even, Odd] at h₂
  obtain ⟨i, rfl⟩ := h₂
  rw [Nat.succ_eq_add_one, add_assoc, ← two_mul, ← mul_add, ← bit0_eq_two_mul, Nat.bit0_div_two]
  specialize ih _ hC'
  rw [← bit0_eq_two_mul, ← bit1, Nat.bit1_div_two] at ih
  refine' ih.trans' _
  rw [← add_assoc, add_right_comm, add_le_add_iff_right]
  split_ifs at hC  with h₂ h₃ h₄
  · rw [← hC]
    refine' book_config.get_book_snd_card_le_X _
    exact book_config.get_book_condition hk hl h₂
  · let x := C'.get_central_vertex μ (C'.get_central_vertex_condition h₁ h₂)
    rw [← hC]
    have : (red_neighbors χ) x ∩ C'.X ⊆ C'.X.erase x :=
      by
      rw [subset_erase]
      refine' ⟨inter_subset_right _ _, _⟩
      simp [not_mem_col_neighbors]
    refine' (add_le_add_right (card_le_of_subset this) _).trans _
    rw [card_erase_add_one]
    exact book_config.get_central_vertex_mem_X _ _ _
  · let x := C'.get_central_vertex μ (C'.get_central_vertex_condition h₁ h₂)
    rw [← hC]
    have : (blue_neighbors χ) x ∩ C'.X ⊆ C'.X.erase x :=
      by
      rw [subset_erase]
      refine' ⟨inter_subset_right _ _, _⟩
      simp [not_mem_col_neighbors]
    refine' (add_le_add_right (card_le_of_subset this) _).trans _
    rw [card_erase_add_one]
    exact book_config.get_central_vertex_mem_X _ _ _

theorem algorithmOption_terminates (μ : ℝ) (ini : BookConfig χ) (hk : k ≠ 0) (hl : l ≠ 0) :
    ∃ i, algorithmOption μ k l ini (i + 1) = none :=
  by
  refine' ⟨bit0 (ini.X.card + 1), _⟩
  rw [Option.eq_none_iff_forall_not_mem]
  intro C hC
  rw [Option.mem_def] at hC
  have := algorithm_option_X_weak_bound C hk hl hC
  rw [← bit1, Nat.bit1_div_two] at this
  linarith only [this]

/-- The index of the final step. Also the number of steps the algorithm takes.
The previous two sentences may have an off-by-one error.  -/
noncomputable def finalStep (μ : ℝ) (k l : ℕ) (ini : BookConfig χ) : ℕ :=
  sInf {i | algorithmOption μ k l ini (i + 1) = none}

/-- The book algorithm. `algorithm μ k l ini i` is the state of the algorithm after the `i`th step,
when initialised with `μ`, `k, l` and initial configuration `ini`.

If we are *after* the termination has applied, this just gives `ini`. That is, this is the correct
definition of the book algorithm *as long as* `i ≤ final_step μ k l ini`, in other words it's
correct as long as the book algorithm hasn't finished.
-/
noncomputable def algorithm (μ : ℝ) (k l : ℕ) (ini : BookConfig χ) (i : ℕ) : BookConfig χ :=
  (algorithmOption μ k l ini i).getD ini

/-- The configuration at the end of the book algorithm. -/
noncomputable def endState (μ : ℝ) (k l : ℕ) (ini : BookConfig χ) : BookConfig χ :=
  algorithm μ k l ini (finalStep μ k l ini)

variable {i : ℕ}

theorem finalStep_is_none (hk : k ≠ 0) (hl : l ≠ 0) :
    algorithmOption μ k l ini (finalStep μ k l ini + 1) = none :=
  haveI : {i | algorithm_option μ k l ini (i + 1) = none}.Nonempty :=
    by
    obtain ⟨i, hi⟩ := algorithm_option_terminates μ ini hk hl
    exact ⟨i, hi⟩
  csInf_mem this

theorem algorithm_zero : algorithm μ k l ini 0 = ini :=
  by
  rw [← Option.some_inj, algorithm, algorithm_option]
  rfl

theorem some_algorithm_of_finalStep_le (hi : i ≤ finalStep μ k l ini) :
    some (algorithm μ k l ini i) = algorithmOption μ k l ini i :=
  by
  cases i
  · rw [algorithm_zero]
    rfl
  rw [Nat.succ_eq_add_one] at *
  rw [algorithm, Option.getD_of_ne_none]
  intro hi'
  have : i ∈ {i | algorithm_option μ k l ini (i + 1) = none} := hi'
  have : final_step μ k l ini ≤ i := Nat.sInf_le this
  linarith

theorem condition_fails_at_end (hk : k ≠ 0) (hl : l ≠ 0) :
    (endState μ k l ini).X.card ≤ ramseyNumber ![k, ⌈(l : ℝ) ^ (3 / 4 : ℝ)⌉₊] ∨
      (endState μ k l ini).p ≤ 1 / k :=
  by
  by_contra h
  have h' : some (end_state μ k l ini) = algorithm_option μ k l ini (final_step μ k l ini) :=
    some_algorithm_of_final_step_le le_rfl
  have : algorithm_option μ k l ini _ = none := final_step_is_none hk hl
  rw [algorithm_option, ← h', algorithm_option._match_1] at this
  simpa only [dif_neg h] using this

theorem succeed_of_finalStep_le' (hi : i < finalStep μ k l ini) :
    ¬((algorithm μ k l ini i).X.card ≤ ramseyNumber ![k, ⌈(l : ℝ) ^ (3 / 4 : ℝ)⌉₊] ∨
        (algorithm μ k l ini i).p ≤ 1 / k) :=
  by
  intro h''
  have h : some (algorithm μ k l ini i) = algorithm_option μ k l ini i :=
    some_algorithm_of_final_step_le hi.le
  have h' : some (algorithm μ k l ini (i + 1)) = algorithm_option μ k l ini (i + 1) :=
    some_algorithm_of_final_step_le hi
  rw [algorithm_option, ← h, algorithm_option._match_1, dif_pos h''] at h'
  simpa only using h'

theorem ramseyNumber_lt_of_lt_finalStep (hi : i < finalStep μ k l ini) :
    ramseyNumber ![k, ⌈(l : ℝ) ^ (3 / 4 : ℝ)⌉₊] < (algorithm μ k l ini i).X.card :=
  by
  have := succeed_of_final_step_le' hi
  rw [not_or, not_le] at this
  exact this.1

theorem one_div_k_lt_p_of_lt_finalStep (hi : i < finalStep μ k l ini) :
    1 / (k : ℝ) < (algorithm μ k l ini i).p :=
  by
  have := succeed_of_final_step_le' hi
  rw [not_or, not_le, not_le] at this
  exact this.2

theorem algorithm_succ (hi : i < finalStep μ k l ini) :
    algorithm μ k l ini (i + 1) =
      let C := algorithm μ k l ini i
      if Even i then C.degreeRegularisationStep k ini.p
      else
        if h' : ramseyNumber ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊] ≤ C.numBigBlues μ then C.bigBlueStep μ
        else
          let x :=
            C.getCentralVertex μ (C.get_central_vertex_condition (succeed_of_finalStep_le' hi) h')
          if
              C.p - αFunction k (height k ini.p C.p) ≤
                (red_density χ) ((red_neighbors χ) x ∩ C.X) ((red_neighbors χ) x ∩ C.y) then
            C.redStepBasic x (C.getCentralVertex_mem_x _ _)
          else C.densityBoostStepBasic x (C.getCentralVertex_mem_x _ _) :=
  by
  have : some (algorithm μ k l ini i) = algorithm_option μ k l ini i :=
    some_algorithm_of_final_step_le hi.le
  rw [← Option.some_inj, some_algorithm_of_final_step_le hi, algorithm_option, ← this,
    algorithm_option._match_1, dif_neg (succeed_of_final_step_le' hi)]

/-- The set of degree regularisation steps. Note this is indexed differently than the paper. -/
noncomputable def degreeSteps (μ : ℝ) (k l : ℕ) (ini : BookConfig χ) : Finset ℕ :=
  (range (finalStep μ k l ini)).filterₓ Even

/-- The set of big blue steps. Note this is indexed differently than the paper. -/
noncomputable def bigBlueSteps (μ : ℝ) (k l : ℕ) (ini : BookConfig χ) : Finset ℕ :=
  (range (finalStep μ k l ini)).filterₓ fun i =>
    ¬Even i ∧ ramseyNumber ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊] ≤ (algorithm μ k l ini i).numBigBlues μ

/-- The set of red or density steps. Note this is indexed differently than the paper. -/
noncomputable def redOrDensitySteps (μ : ℝ) (k l : ℕ) (ini : BookConfig χ) : Finset ℕ :=
  (range (finalStep μ k l ini)).filterₓ fun i =>
    ¬Even i ∧ (algorithm μ k l ini i).numBigBlues μ < ramseyNumber ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊]

theorem degreeSteps_disjoint_bigBlueSteps_union_redOrDensitySteps :
    Disjoint (degreeSteps μ k l ini) (bigBlueSteps μ k l ini ∪ redOrDensitySteps μ k l ini) :=
  by
  rw [big_blue_steps, red_or_density_steps, ← filter_or, degree_steps, disjoint_filter]
  intro i hi
  rw [← and_or_left, not_and', Classical.not_not]
  exact Function.const _

theorem bigBlueSteps_disjoint_redOrDensitySteps :
    Disjoint (bigBlueSteps μ k l ini) (redOrDensitySteps μ k l ini) :=
  by
  rw [big_blue_steps, red_or_density_steps, disjoint_filter]
  rintro x hx ⟨hx₁, hx₂⟩
  rw [not_and, not_lt]
  intro
  exact hx₂

theorem of_mem_red_or_density_steps₁ {i : ℕ} (hi : i ∈ redOrDensitySteps μ k l ini) :
    ¬((algorithm μ k l ini i).X.card ≤ ramseyNumber ![k, ⌈(l : ℝ) ^ (3 / 4 : ℝ)⌉₊] ∨
        (algorithm μ k l ini i).p ≤ 1 / k) :=
  by
  rw [red_or_density_steps, mem_filter, mem_range] at hi
  exact succeed_of_final_step_le' hi.1

theorem of_mem_red_or_density_steps₂ {i : ℕ} (hi : i ∈ redOrDensitySteps μ k l ini) :
    ¬ramseyNumber ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊] ≤ (algorithm μ k l ini i).numBigBlues μ :=
  by
  rw [red_or_density_steps, mem_filter, ← not_le] at hi
  exact hi.2.2

/-- The choice of `x` in a red or density step. -/
noncomputable def getX (hi : i ∈ redOrDensitySteps μ k l ini) : V :=
  (algorithm μ k l ini i).getCentralVertex μ
    ((algorithm μ k l ini i).get_central_vertex_condition (of_mem_red_or_density_steps₁ hi)
      (of_mem_red_or_density_steps₂ hi))

theorem getX_mem_centralVertices (i : ℕ) (hi : i ∈ redOrDensitySteps μ k l ini) :
    getX hi ∈ (algorithm μ k l ini i).centralVertices μ :=
  (algorithm μ k l ini i).getCentralVertex_mem _ _

/-- The set of red steps. -/
noncomputable def redSteps (μ : ℝ) (k l : ℕ) (ini : BookConfig χ) : Finset ℕ :=
  Finset.image coe <|
    (redOrDensitySteps μ k l ini).attach.filterₓ fun i =>
      let x := getX i.Prop
      let C := algorithm μ k l ini i
      C.p - αFunction k (height k ini.p C.p) ≤
        (red_density χ) ((red_neighbors χ) x ∩ C.X) ((red_neighbors χ) x ∩ C.y)

/-- The set of density boost steps. -/
noncomputable def densitySteps (μ : ℝ) (k l : ℕ) (ini : BookConfig χ) : Finset ℕ :=
  Finset.image coe <|
    (redOrDensitySteps μ k l ini).attach.filterₓ fun i =>
      let x := getX i.Prop
      let C := algorithm μ k l ini i
      (red_density χ) ((red_neighbors χ) x ∩ C.X) ((red_neighbors χ) x ∩ C.y) <
        C.p - αFunction k (height k ini.p C.p)

theorem redSteps_subset_redOrDensitySteps : redSteps μ k l ini ⊆ redOrDensitySteps μ k l ini :=
  by
  intro i hi
  rw [red_steps] at hi
  simp only [mem_image, exists_prop, mem_filter, mem_attach, Subtype.exists, exists_eq_right,
    true_and_iff, exists_eq_right, exists_and_right, Subtype.coe_mk] at hi
  obtain ⟨hi, -⟩ := hi
  exact hi

theorem densitySteps_subset_redOrDensitySteps :
    densitySteps μ k l ini ⊆ redOrDensitySteps μ k l ini :=
  by
  intro i hi
  rw [density_steps] at hi
  simp only [mem_image, exists_prop, mem_filter, mem_attach, Subtype.exists, exists_eq_right,
    true_and_iff, exists_eq_right, exists_and_right, Subtype.coe_mk] at hi
  obtain ⟨hi, -⟩ := hi
  exact hi

theorem redSteps_union_densitySteps :
    redSteps μ k l ini ∪ densitySteps μ k l ini = redOrDensitySteps μ k l ini :=
  by
  refine'
    subset.antisymm
      (union_subset red_steps_subset_red_or_density_steps density_steps_subset_red_or_density_steps)
      _
  rw [red_steps, density_steps, ← image_union, ← filter_or]
  intro i hi
  simp only [mem_image, Subtype.exists, Subtype.coe_mk, exists_prop, mem_filter, mem_attach,
    true_and_iff, exists_eq_right, exists_and_right]
  refine' ⟨hi, _⟩
  exact le_or_lt _ _

theorem redSteps_disjoint_densitySteps : Disjoint (redSteps μ k l ini) (densitySteps μ k l ini) :=
  by
  rw [red_steps, density_steps, disjoint_image Subtype.coe_injective, disjoint_filter]
  intro x hx
  simp

theorem degree_regularisation_applied {i : ℕ} (hi : i ∈ degreeSteps μ k l ini) :
    algorithm μ k l ini (i + 1) = (algorithm μ k l ini i).degreeRegularisationStep k ini.p :=
  by
  rw [degree_steps, mem_filter, mem_range] at hi
  rw [algorithm_succ hi.1]
  exact if_pos hi.2

theorem big_blue_applied {i : ℕ} (hi : i ∈ bigBlueSteps μ k l ini) :
    algorithm μ k l ini (i + 1) = (algorithm μ k l ini i).bigBlueStep μ :=
  by
  rw [big_blue_steps, mem_filter, mem_range] at hi
  rw [algorithm_succ hi.1]
  dsimp
  rw [if_neg hi.2.1, dif_pos hi.2.2]

theorem red_applied {i : ℕ} (hi : i ∈ redSteps μ k l ini) :
    algorithm μ k l ini (i + 1) =
      (algorithm μ k l ini i).redStepBasic (getX (redSteps_subset_redOrDensitySteps hi))
        (BookConfig.getCentralVertex_mem_x _ _ _) :=
  by
  rw [red_steps, mem_image] at hi
  simp only [Subtype.coe_mk, mem_filter, mem_attach, true_and_iff, exists_prop, Subtype.exists,
    exists_and_right, exists_eq_right] at hi
  obtain ⟨hi', hi''⟩ := hi
  rw [red_or_density_steps, mem_filter, ← not_le, mem_range] at hi'
  rw [algorithm_succ hi'.1]
  dsimp
  rw [if_neg hi'.2.1, dif_neg hi'.2.2, if_pos]
  · rfl
  · exact hi''

theorem density_applied {i : ℕ} (hi : i ∈ densitySteps μ k l ini) :
    algorithm μ k l ini (i + 1) =
      (algorithm μ k l ini i).densityBoostStepBasic
        (getX (densitySteps_subset_redOrDensitySteps hi))
        (BookConfig.getCentralVertex_mem_x _ _ _) :=
  by
  rw [density_steps, mem_image] at hi
  simp only [Subtype.coe_mk, mem_filter, mem_attach, true_and_iff, exists_prop, Subtype.exists,
    exists_and_right, exists_eq_right] at hi
  obtain ⟨hi', hi''⟩ := hi
  rw [red_or_density_steps, mem_filter, ← not_le, mem_range] at hi'
  rw [algorithm_succ hi'.1]
  dsimp
  rw [if_neg hi'.2.1, dif_neg hi'.2.2, if_neg]
  · rfl
  · rwa [not_le]

theorem union_partial_steps :
    redOrDensitySteps μ k l ini ∪ bigBlueSteps μ k l ini ∪ degreeSteps μ k l ini =
      range (finalStep μ k l ini) :=
  by
  rw [red_or_density_steps, big_blue_steps, ← filter_or, degree_steps, ← filter_or]
  refine' filter_true_of_mem _
  intro i hi
  rw [← and_or_left, and_iff_left]
  · exact em' _
  exact lt_or_le _ _

theorem union_steps :
    redSteps μ k l ini ∪ bigBlueSteps μ k l ini ∪ densitySteps μ k l ini ∪ degreeSteps μ k l ini =
      range (finalStep μ k l ini) :=
  by rw [union_right_comm (red_steps _ _ _ _), red_steps_union_density_steps, union_partial_steps]

theorem filter_even_thing {n : ℕ} :
    ((range n).filterₓ Even).card ≤ ((range n).filterₓ fun i => ¬Even i).card + 1 :=
  by
  have : ((range n).filterₓ Even).image Nat.succ ⊆ (range (n + 1)).filterₓ fun i => ¬Even i :=
    by
    simp only [Finset.subset_iff, mem_filter, mem_image, and_imp, exists_prop, and_assoc',
      mem_range, forall_exists_index, Nat.succ_eq_add_one]
    rintro _ y hy hy' rfl
    simp [hy, hy', parity_simps]
  rw [← Finset.card_image_of_injective _ Nat.succ_injective]
  refine' (card_le_of_subset this).trans _
  rw [range_succ, filter_insert]
  split_ifs
  · exact Nat.le_succ _
  exact card_insert_le _ _

theorem num_degreeSteps_le_add :
    (degreeSteps μ k l ini).card ≤
      (redSteps μ k l ini).card + (bigBlueSteps μ k l ini).card + (densitySteps μ k l ini).card +
        1 :=
  by
  have :
    big_blue_steps μ k l ini ∪ red_or_density_steps μ k l ini =
      (range (final_step μ k l ini)).filterₓ fun i => ¬Even i :=
    by
    rw [big_blue_steps, red_or_density_steps, ← filter_or]
    refine' filter_congr _
    intro i hi
    rw [← and_or_left, ← not_le, and_iff_left]
    exact em _
  rw [add_right_comm _ _ (Finset.card _), ← card_disjoint_union red_steps_disjoint_density_steps,
    red_steps_union_density_steps, add_comm _ (Finset.card _), ←
    card_disjoint_union big_blue_steps_disjoint_red_or_density_steps, this, degree_steps]
  apply filter_even_thing

theorem cases_of_lt_finalStep {i : ℕ} (hi : i < finalStep μ k l ini) :
    i ∈ redSteps μ k l ini ∨
      i ∈ bigBlueSteps μ k l ini ∨ i ∈ densitySteps μ k l ini ∨ i ∈ degreeSteps μ k l ini :=
  by rwa [← mem_range, ← union_steps, mem_union, mem_union, mem_union, or_assoc', or_assoc'] at hi

-- (7)
theorem x_subset {i : ℕ} (hi : i < finalStep μ k l ini) :
    (algorithm μ k l ini (i + 1)).X ⊆ (algorithm μ k l ini i).X :=
  by
  rcases cases_of_lt_final_step hi with (hi' | hi' | hi' | hi')
  · rw [red_applied hi', book_config.red_step_basic_X]
    exact inter_subset_right _ _
  · rw [big_blue_applied hi', book_config.big_blue_step_X]
    exact book_config.get_book_snd_subset
  · rw [density_applied hi', book_config.density_boost_step_basic_X]
    exact inter_subset_right _ _
  · rw [degree_regularisation_applied hi', book_config.degree_regularisation_step_X]
    exact book_config.degree_regularisation_step_X_subset

-- (7)
theorem y_subset {i : ℕ} (hi : i < finalStep μ k l ini) :
    (algorithm μ k l ini (i + 1)).y ⊆ (algorithm μ k l ini i).y :=
  by
  rcases cases_of_lt_final_step hi with (hi' | hi' | hi' | hi')
  · rw [red_applied hi', book_config.red_step_basic_Y]
    exact inter_subset_right _ _
  · rw [big_blue_applied hi', book_config.big_blue_step_Y]
    rfl
  · rw [density_applied hi', book_config.density_boost_step_basic_Y]
    exact inter_subset_right _ _
  · rw [degree_regularisation_applied hi', book_config.degree_regularisation_step_Y]
    rfl

theorem a_subset {i : ℕ} (hi : i < finalStep μ k l ini) :
    (algorithm μ k l ini i).A ⊆ (algorithm μ k l ini (i + 1)).A :=
  by
  rcases cases_of_lt_final_step hi with (hi' | hi' | hi' | hi')
  · rw [red_applied hi', book_config.red_step_basic_A]
    exact subset_insert _ _
  · rw [big_blue_applied hi', book_config.big_blue_step_A]
    rfl
  · rw [density_applied hi', book_config.density_boost_step_basic_A]
    rfl
  · rw [degree_regularisation_applied hi', book_config.degree_regularisation_step_A]
    rfl

theorem b_subset {i : ℕ} (hi : i < finalStep μ k l ini) :
    (algorithm μ k l ini i).B ⊆ (algorithm μ k l ini (i + 1)).B :=
  by
  rcases cases_of_lt_final_step hi with (hi' | hi' | hi' | hi')
  · rw [red_applied hi', book_config.red_step_basic_B]
    rfl
  · rw [big_blue_applied hi', book_config.big_blue_step_B]
    exact subset_union_left _ _
  · rw [density_applied hi', book_config.density_boost_step_basic_B]
    exact subset_insert _ _
  · rw [degree_regularisation_applied hi', book_config.degree_regularisation_step_B]
    rfl

/-- Define `β` from the paper. -/
noncomputable def blueXRatio (μ : ℝ) (k l : ℕ) (ini : BookConfig χ) (i : ℕ) : ℝ :=
  if h : i ∈ redOrDensitySteps μ k l ini then
    ((blue_neighbors χ) (getX h) ∩ (algorithm μ k l ini i).X).card / (algorithm μ k l ini i).X.card
  else 0

theorem blueXRatio_eq (hi : i ∈ redOrDensitySteps μ k l ini) :
    blueXRatio μ k l ini i =
      ((blue_neighbors χ) (getX hi) ∩ (algorithm μ k l ini i).X).card /
        (algorithm μ k l ini i).X.card :=
  dif_pos hi

-- (8)
theorem blueXRatio_prop (hi : i ∈ redOrDensitySteps μ k l ini) :
    blueXRatio μ k l ini i * (algorithm μ k l ini i).X.card =
      ((blue_neighbors χ) (getX hi) ∩ (algorithm μ k l ini i).X).card :=
  by
  cases' Finset.eq_empty_or_nonempty (algorithm μ k l ini i).X with hX hX
  · rw [hX, inter_empty, card_empty, Nat.cast_zero, MulZeroClass.mul_zero]
  rw [blue_X_ratio, dif_pos hi, div_mul_cancel]
  rwa [Nat.cast_ne_zero, ← pos_iff_ne_zero, card_pos]

theorem blueXRatio_nonneg : 0 ≤ blueXRatio μ k l ini i := by rw [blue_X_ratio];
  split_ifs <;> positivity

theorem blueXRatio_le_mu (hi : i ∈ redOrDensitySteps μ k l ini) : blueXRatio μ k l ini i ≤ μ :=
  by
  rw [blue_X_ratio_eq hi]
  have := get_x_mem_central_vertices i hi
  rw [book_config.central_vertices, mem_filter] at this
  rw [div_le_iff]
  · exact this.2
  rw [red_or_density_steps, mem_filter, mem_range] at hi
  rw [Nat.cast_pos]
  refine' (ramsey_number_lt_of_lt_final_step hi.1).trans_le' _
  exact Nat.zero_le _

end SimpleGraph

