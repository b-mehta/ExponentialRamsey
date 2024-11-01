/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Data.Nat.Choose.Central

/-!
# Stuff for data.nat.choose.central
-/


section

theorem centralBinom_monotone : Monotone Nat.centralBinom := fun n _ h =>
  (Nat.choose_le_choose n (Nat.mul_le_mul_left 2 h)).trans (Nat.choose_le_centralBinom _ _)

end

