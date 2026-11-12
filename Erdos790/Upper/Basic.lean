import Erdos790.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The full upper-bound target for Erdős 790

The lower-bound theorem is Samuel Korsky's theorem. This file fixes the
distinct-summand upper-bound interface used by the new construction.
-/

open Finset Filter

namespace Erdos790

/-- An explicit host whose every sum-free subset has cardinality at most `bound`. -/
def UpperWitness (n : ℕ) (bound : ℝ) : Prop :=
  ∃ A : Finset ℤ, A.card = n ∧
    ∀ B ⊆ A, IsSumFree B → (B.card : ℝ) ≤ bound

theorem UpperWitness.le {n : ℕ} {bound : ℝ} (h : UpperWitness n bound) :
    (l n : ℝ) ≤ bound := by
  obtain ⟨A, hA, hbound⟩ := h
  obtain ⟨B, hBA, hB, hcard⟩ := l_spec n A hA
  exact (Nat.cast_le.mpr hcard).trans (hbound B hBA hB)

/-- The complete matching-order assertion, with the original integer-host scope. -/
def MatchingOrder : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
    ∀ᶠ n : ℕ in atTop,
      c * n / Real.log n ^ 2 ≤ (l n : ℝ) ∧
      (l n : ℝ) ≤ C * n / Real.log n ^ 2

namespace Upper

/-- Avoiding sums of between two and `R` terms, with repetitions permitted.

The multiplicity function is used only on the finite host `B`.
-/
def RepeatedSumFree (R : ℕ) (B : Finset ℕ) : Prop :=
  ∀ a ∈ B, ∀ multiplicity : ℕ → ℕ,
    2 ≤ ∑ b ∈ B, multiplicity b →
    (∑ b ∈ B, multiplicity b) ≤ R →
    (∑ b ∈ B, multiplicity b * b) ≠ a

theorem RepeatedSumFree.arity_mono {R S : ℕ} {B : Finset ℕ}
    (hB : RepeatedSumFree R B) (hSR : S ≤ R) : RepeatedSumFree S B := by
  intro a ha multiplicity hlower hupper
  exact hB a ha multiplicity hlower (hupper.trans hSR)

end Upper
end Erdos790
