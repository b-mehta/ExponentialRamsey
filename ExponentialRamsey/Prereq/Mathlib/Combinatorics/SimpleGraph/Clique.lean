/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import ExponentialRamsey.Prereq.Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Stuff for combinatorics.simple_graph.clique
-/

namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {n : ℕ}

theorem not_cliqueFree_iff' (n : ℕ) : ¬G.CliqueFree n ↔ Nonempty ((⊤ : SimpleGraph (Fin n)) →g G) :=
  by rw [not_cliqueFree_iff, SimpleGraph.topHomGraphEquiv.nonempty_congr]

theorem cliqueFree_iff' {n : ℕ} : G.CliqueFree n ↔ IsEmpty ((⊤ : SimpleGraph (Fin n)) →g G) := by
  rw [← not_iff_not, not_cliqueFree_iff', not_isEmpty_iff]

theorem CliqueFree.hom (f : G →g H) : H.CliqueFree n → G.CliqueFree n := fun h =>
  cliqueFree_iff'.2 ⟨fun x => (cliqueFree_iff'.1 h).elim' (f.comp x)⟩

end SimpleGraph
