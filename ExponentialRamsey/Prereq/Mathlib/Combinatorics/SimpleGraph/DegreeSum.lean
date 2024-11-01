/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Stuff for combinatorics.simple_graph.degree_sum
-/


namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

open Fintype (card)

open Finset

section

theorem exists_even_degree [Fintype V] [DecidableRel G.Adj] (hV : Odd (card V)) :
    ∃ v : V, Even (G.degree v) := by
  have : (univ.filter (Odd <| G.degree ·)) ≠ univ := by
    rw [←card_lt_iff_ne_univ, (card_le_univ _).lt_iff_ne]
    intro h
    have h' := even_card_odd_degree_vertices G
    rw [h, ← Nat.not_odd_iff_even] at h'
    exact h' hV
  rw [Ne.eq_def, filter_eq_self] at this
  simpa using this

end

end SimpleGraph

