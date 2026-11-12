import Erdos790JSP.OriginalStatement
import Erdos790

open Finset Filter
open scoped Topology

namespace Erdos790JSP

theorem safe_iff (B : Finset ℤ) :
    Erdos790Original.Safe B ↔ Erdos790.IsSumFree B := by
  constructor
  · intro h b hb S hS hcard
    apply h S (hS.trans (Finset.erase_subset b B)) hcard b hb
    intro hbS
    exact (Finset.mem_erase.mp (hS hbS)).1 rfl
  · intro h S hSB hcard b hb hbS
    apply h b hb S ?_ hcard
    intro x hx
    apply Finset.mem_erase.mpr
    constructor
    · intro hxb
      subst x
      exact hbS hx
    · exact hSB hx

theorem guaranteed_iff (n m : ℕ) :
    Erdos790Original.Guaranteed n m ↔ m ∈ Erdos790.admissible n := by
  constructor
  · intro h A hA
    obtain ⟨B, hBA, hB, hm⟩ := h A hA
    exact ⟨B, hBA, (safe_iff B).mp hB, hm⟩
  · intro h A hA
    obtain ⟨B, hBA, hB, hm⟩ := h A hA
    exact ⟨B, hBA, (safe_iff B).mpr hB, hm⟩

theorem extremal_eq (n : ℕ) : Erdos790Original.extremal n = Erdos790.l n := by
  unfold Erdos790Original.extremal Erdos790.l
  congr 1
  ext m
  exact guaranteed_iff n m

theorem matching_order : Erdos790Original.MatchingOrder := by
  simpa only [Erdos790Original.MatchingOrder, Erdos790.MatchingOrder, extremal_eq]
    using Erdos790.matching_order

theorem upper_bound : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ n : ℕ in atTop, (Erdos790Original.extremal n : ℝ) ≤ C * n / Real.log n ^ 2 := by
  simpa only [extremal_eq] using Erdos790.matching_upper_bound

theorem lower_bound : ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n →
    c * n / Real.log n ^ 2 ≤ (Erdos790Original.extremal n : ℝ) := by
  simpa only [extremal_eq] using Erdos790.korsky

theorem first_question :
    Tendsto (fun n : ℕ => (Erdos790Original.extremal n : ℝ) / Real.sqrt n)
      atTop atTop := by
  simpa only [extremal_eq] using Erdos790.erdos_790_part_i

theorem second_question :
    ¬ ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (Erdos790Original.extremal n : ℝ) < (n : ℝ) ^ (1 - c) := by
  simpa only [extremal_eq] using Erdos790.erdos_790_part_ii

theorem exponent :
    Tendsto (fun n : ℕ => Real.log (Erdos790Original.extremal n) / Real.log n)
      atTop (𝓝 1) := by
  simpa only [extremal_eq] using Erdos790.erdos_790_exponent

end Erdos790JSP
