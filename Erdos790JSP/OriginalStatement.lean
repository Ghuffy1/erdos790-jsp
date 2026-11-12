import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Int.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
An independent statement of the finite integer-set problem.
This module imports trusted libraries and no submitted Erdos790 definitions.
-/

open Finset Filter
open scoped Topology

namespace Erdos790Original

def Safe (B : Finset ℤ) : Prop :=
  ∀ S : Finset ℤ, S ⊆ B → 2 ≤ S.card →
    ∀ b ∈ B, b ∉ S → ∑ x ∈ S, x ≠ b

def Guaranteed (n m : ℕ) : Prop :=
  ∀ A : Finset ℤ, A.card = n →
    ∃ B : Finset ℤ, B ⊆ A ∧ Safe B ∧ m ≤ B.card

noncomputable def extremal (n : ℕ) : ℕ :=
  sSup {m : ℕ | Guaranteed n m}

def MatchingOrder : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
    ∀ᶠ n : ℕ in atTop,
      c * n / Real.log n ^ 2 ≤ (extremal n : ℝ) ∧
      (extremal n : ℝ) ≤ C * n / Real.log n ^ 2

end Erdos790Original
