/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Analysis.SpecialFunctions.Log.Base
import Analysis.SpecialFunctions.Log.Deriv

#align_import prereq.mathlib.analysis.special_functions.log.base

/-!
# Stuff for analysis.special_functions.log.base
-/


namespace Real

theorem HasDerivAt.logb {f : ℝ → ℝ} {x b f' : ℝ} (hf : HasDerivAt f f' x) (hx : f x ≠ 0) :
    HasDerivAt (fun y => logb b (f y)) (f' / (f x * log b)) x := by
  simpa [div_div] using (hf.log hx).div_const (log b)

-- TODO (BM): change to `⁻¹` rather than `1 /`
theorem hasDerivAt_logb {x b : ℝ} (hx : x ≠ 0) : HasDerivAt (logb b) (1 / (x * log b)) x :=
  (hasDerivAt_id' _).logb hx

end Real

