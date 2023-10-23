/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Combinatorics.SimpleGraph.Basic
import Combinatorics.SimpleGraph.Clique
import Prereq.Mathlib.Combinatorics.SimpleGraph.Basic

#align_import prereq.mathlib.combinatorics.simple_graph.clique

/-!
# Stuff for combinatorics.simple_graph.clique
-/


namespace SimpleGraph

variable {V W : Type _} {G : SimpleGraph V} {H : SimpleGraph W} {n : ℕ}

theorem not_cliqueFree_iff' (n : ℕ) : ¬G.CliqueFree n ↔ Nonempty ((⊤ : SimpleGraph (Fin n)) →g G) :=
  by rw [not_clique_free_iff, SimpleGraph.topHomGraphEquiv.nonempty_congr]

theorem cliqueFree_iff' {n : ℕ} : G.CliqueFree n ↔ IsEmpty ((⊤ : SimpleGraph (Fin n)) →g G) := by
  rw [← not_iff_not, not_clique_free_iff', not_isEmpty_iff]

theorem CliqueFree.hom (f : G →g H) : H.CliqueFree n → G.CliqueFree n := fun h =>
  cliqueFree_iff'.2 ⟨fun x => (cliqueFree_iff'.1 h).elim' (f.comp x)⟩

end SimpleGraph

