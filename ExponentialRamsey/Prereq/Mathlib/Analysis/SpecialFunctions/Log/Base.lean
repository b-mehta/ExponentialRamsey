/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Stuff for analysis.special_functions.log.base
-/


theorem HasDerivAt.logb {f : ℝ → ℝ} {x b f' : ℝ} (hf : HasDerivAt f f' x) (hx : f x ≠ 0) :
    HasDerivAt (fun y => Real.logb b (f y)) (f' / (f x * Real.log b)) x := by
  simpa [div_div] using (hf.log hx).div_const (Real.log b)

namespace Real

-- TODO (BM): change to `⁻¹` rather than `1 /`
theorem hasDerivAt_logb {x b : ℝ} (hx : x ≠ 0) : HasDerivAt (Real.logb b) (1 / (x * Real.log b)) x :=
  (hasDerivAt_id' _).logb hx

end Real
