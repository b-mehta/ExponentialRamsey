import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Stuff for data.choose.multinomial
-/

namespace Nat

open Finset

theorem multinomial_rec {K : Type*} [DecidableEq K] [Fintype K] {f : K → ℕ} (h : ∀ k, 0 < f k)
  {S : Finset K} (nenS : S.Nonempty) :
    multinomial S f = ∑ i ∈ S, multinomial S (Function.update f i (f i - 1)) := by
  let decrement_at (l : K) := Function.update f l (f l - 1)
  have sum_decrement_at {l : K} (lS : l ∈ S) :
      ∑ k ∈ S, decrement_at l k = ∑ k ∈ S, f k - 1 := by
    simp only [decrement_at, sum_update_of_mem lS, sdiff_singleton_eq_erase, add_comm]
    rw [← Nat.add_sub_assoc (h l), sum_erase_add _ _ lS]
  have uf (x : K) := Nat.mul_div_mul_left (∑ i ∈ S, f i - 1)! (∏ i ∈ S, (decrement_at x i)!) (h x)
  have prod_decr (x : K) (xS : x ∈ S) : f x * ∏ i ∈ S, (decrement_at x i)! = ∏ i ∈ S, (f i)! := by
    simp_rw [decrement_at, Function.update_apply, apply_ite, prod_ite, prod_const, ← mul_assoc]
    have eq_sngl : S.filter (fun x_1 => x_1 = x) = {x} := by simp [filter_eq']; intro; contradiction
    rw [eq_sngl, card_singleton, pow_one, mul_factorial_pred (ne_of_gt (h x)),
      ← prod_singleton (fun x => (f x)!), ← eq_sngl, prod_filter_mul_prod_filter_not]
  unfold multinomial
  rw [← mul_factorial_pred (sum_pos (fun i _ => h i) (nenS)).ne']
  have {e : K → ℕ} (i : K) (iS : i ∈ S) : -- i wish i knew a nicer way to do this
      (∑ k ∈ S, decrement_at i k)! / e i = (∑ k ∈ S, f k - 1)! / e i := by
    simp [sum_decrement_at iS]
  simp [sum_mul, decrement_at, sum_congr rfl this, ← uf]
  have {a : ℕ} (x : K) (xS : x ∈ S): -- same
      f x * a / (f x * ∏ i ∈ S, (decrement_at x i)!) = f x * a / ∏ i ∈ S, (f i)! := by
    simp [prod_decr _ xS]
  rw [sum_congr rfl this]
  refine Nat.sum_div (fun i iS => ?_)
  rw [← prod_decr i iS]
  apply mul_dvd_mul_left
  rw [← sum_decrement_at iS]
  exact prod_factorial_dvd_factorial_sum _ _

end Nat
