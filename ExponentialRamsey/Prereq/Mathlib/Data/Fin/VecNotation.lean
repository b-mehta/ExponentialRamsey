/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Data.Fin.VecNotation

/-!
# Stuff for data.fin.vec_notation
-/


namespace Function

open Matrix (vecCons)

open Fin

theorem update_head {α : Type*} {i : ℕ} {x y : α} {t : Fin i → α} :
    update (vecCons x t) 0 y = vecCons y t := by
  rw [funext_iff, Fin.forall_fin_succ]
  refine ⟨rfl, fun j => ?_⟩
  rw [update_of_ne]
  · simp only [vecCons, Fin.cons_succ]
  exact succ_ne_zero j

theorem update_cons_one {α : Type*} {i : ℕ} {x y z : α} {t : Fin i → α} :
    update (vecCons x (vecCons y t)) 1 z = vecCons x (vecCons z t) := by
  simp only [funext_iff, forall_fin_succ]
  refine ⟨rfl, rfl, fun j => ?_⟩
  rw [update_of_ne]
  · simp only [vecCons, cons_succ]
  exact (succ_injective _).ne (Fin.succ_ne_zero _)

theorem update_cons_two {α : Type*} {i : ℕ} {w x y z : α} {t : Fin i → α} :
    update (vecCons w (vecCons x (vecCons y t))) 2 z = vecCons w (vecCons x (vecCons z t)) := by
  simp only [funext_iff, forall_fin_succ]
  refine ⟨rfl, rfl, rfl, fun j => ?_⟩
  rw [update_of_ne]
  · simp only [vecCons, cons_succ]
  exact (succ_injective _).ne ((succ_injective _).ne (succ_ne_zero _))

theorem swap_cons {α : Type*} {i : ℕ} {x y : α} {t : Fin i → α} :
    vecCons x (vecCons y t) ∘ Equiv.swap 0 1 = vecCons y (vecCons x t) := by
  rw [funext_iff]
  simp only [forall_fin_succ]
  refine ⟨rfl, rfl, fun j => ?_⟩
  simp only [vecCons, cons_succ, comp_apply]
  rw [Equiv.swap_apply_of_ne_of_ne, cons_succ, cons_succ]
  · exact succ_ne_zero _
  exact (succ_injective _).ne (succ_ne_zero _)

end Function
