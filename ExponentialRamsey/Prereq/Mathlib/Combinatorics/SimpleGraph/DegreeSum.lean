/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Combinatorics.SimpleGraph.DegreeSum

#align_import prereq.mathlib.combinatorics.simple_graph.degree_sum

/-!
# Stuff for combinatorics.simple_graph.degree_sum
-/


namespace SimpleGraph

variable {V V' : Type _} {G : SimpleGraph V} {K K' : Type _}

open Fintype (card)

open Finset

section

theorem exists_even_degree [Fintype V] [DecidableRel G.Adj] (hV : Odd (card V)) :
    ∃ v : V, Even (G.degree v) :=
  by
  have := even_card_odd_degree_vertices G
  have : (univ.filter fun v : V => Odd (G.degree v)) ≠ univ :=
    by
    rw [← card_lt_iff_ne_univ, lt_iff_le_and_ne]
    refine' ⟨card_le_univ _, _⟩
    intro h
    rw [h, Nat.even_iff_not_odd] at this 
    exact this hV
  rw [Ne.def, filter_eq_self] at this 
  simpa using this

end

end SimpleGraph

