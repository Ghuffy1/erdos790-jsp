import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith

/-!
# Summing the cluster recurrence

The coefficient one half turns a uniform bound on the forcing partial sums
into a uniform bound on the total cluster mass.
-/

open Finset

namespace Erdos790.Upper

theorem recurrence_partial_sums {f a : ℕ → ℝ} {C : ℝ}
    (hf : ∀ n, 0 ≤ f n) (hstep : ∀ n, f (n + 1) ≤ f n / 2 + a n)
    (hforcing : ∀ N, ∑ n ∈ Finset.range N, a n ≤ C) :
    ∀ N, ∑ n ∈ Finset.range N, f n ≤ 2 * (f 0 + C) := by
  intro N
  cases N with
  | zero =>
    have hC := hforcing 0
    simp only [Finset.range_zero, Finset.sum_empty] at hC ⊢
    linarith [hf 0]
  | succ N =>
    have hsum : (∑ n ∈ Finset.range N, f (n + 1)) ≤
        (∑ n ∈ Finset.range N, f n) / 2 + ∑ n ∈ Finset.range N, a n := by
      calc
        (∑ n ∈ Finset.range N, f (n + 1)) ≤
            ∑ n ∈ Finset.range N, (f n / 2 + a n) :=
          Finset.sum_le_sum (fun n _ => hstep n)
        _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_div]
    have hlast := Finset.sum_range_succ f N
    have hfirst := Finset.sum_range_succ' f N
    have hbound := hforcing N
    have hnonneg := hf N
    linarith

theorem recurrence_summable {f a : ℕ → ℝ} {C : ℝ}
    (hf : ∀ n, 0 ≤ f n) (hstep : ∀ n, f (n + 1) ≤ f n / 2 + a n)
    (hforcing : ∀ N, ∑ n ∈ Finset.range N, a n ≤ C) :
    Summable f ∧ ∑' n, f n ≤ 2 * (f 0 + C) := by
  have hpartial := recurrence_partial_sums hf hstep hforcing
  exact ⟨summable_of_sum_range_le hf hpartial,
    Real.tsum_le_of_sum_range_le hf hpartial⟩

end Erdos790.Upper
