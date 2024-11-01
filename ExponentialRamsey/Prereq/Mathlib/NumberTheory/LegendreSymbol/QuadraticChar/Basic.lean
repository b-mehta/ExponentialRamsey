/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Data.Fintype.Parity
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# Stuff for number_theory.legendre_symbol.quadratic_char.basic
-/


open Fintype (card)

open Finset

variable {F : Type*} [Fintype F] [Field F]

theorem symmetric_isSquare (hF : card F % 4 ≠ 3) : Symmetric fun x y : F => IsSquare (x - y) :=
  fun _ _ h => by simpa using h.mul (FiniteField.isSquare_neg_one_iff.2 hF)

theorem card_non_zero_square_non_square [DecidableEq F] (hF : ringChar F ≠ 2) :
    (univ.filter fun x : F => x ≠ 0 ∧ IsSquare x).card = card F / 2 ∧
      (univ.filter fun x : F => ¬IsSquare x).card = card F / 2 :=
  by
  have : (univ.filter fun x : F => ¬IsSquare x) = univ.filter fun x : F => x ≠ 0 ∧ ¬IsSquare x :=
    by
    refine filter_congr ?_
    simp (config := { contextual := true }) [not_imp_not]
  rw [this]
  have cf := quadraticChar_sum_zero hF
  simp only [quadraticChar_apply, quadraticCharFun] at cf
  rw [sum_ite, sum_const_zero, zero_add, sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul,
    mul_neg, mul_one, mul_one, add_neg_eq_zero, Nat.cast_inj, filter_filter, filter_filter] at cf
  rw [← cf, and_self_iff]
  have :
    ((univ.filter fun x : F => x ≠ 0 ∧ IsSquare x) ∪ univ.filter fun x : F => x ≠ 0 ∧ ¬IsSquare x) ∪
        {0} =
      univ :=
    by
    simp only [← filter_or, ← and_or_left, em, and_true, filter_ne']
    rw [union_comm, ← insert_eq, insert_erase]
    exact mem_univ _
  have h' := congr_arg Finset.card this
  rw [card_union_of_disjoint, card_union_of_disjoint, card_singleton, card_univ, ← cf, ← two_mul] at h'
  · rw [← h']
    omega
  · rw [Finset.disjoint_left]
    simp (config := { contextual := true })
  · simp

theorem card_square (F : Type*) [Fintype F] [Field F] [DecidableEq F] (hF : ringChar F ≠ 2) :
    ((univ : Finset F).filter IsSquare).card = card F / 2 + 1 :=
  by
  rw [← (card_non_zero_square_non_square hF).1]
  simp only [and_comm, ← filter_filter, filter_ne']
  rw [card_erase_add_one]
  simp
