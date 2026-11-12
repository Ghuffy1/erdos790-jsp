import Erdos790.Main
import Erdos790.Upper.Basic

namespace Erdos790

/-- Combining an eventual matching upper bound with Korsky's lower theorem. -/
theorem matchingOrder_of_eventual_upper
    (hupper : ∃ C : ℝ, 0 < C ∧
      ∀ᶠ n : ℕ in Filter.atTop, (l n : ℝ) ≤ C * n / Real.log n ^ 2) :
    MatchingOrder := by
  obtain ⟨c, hc, hlower⟩ := korsky
  obtain ⟨C, hC, hupper⟩ := hupper
  refine ⟨c, hc, C, hC, ?_⟩
  filter_upwards [hupper, Filter.eventually_ge_atTop 2] with n hn hn2
  exact ⟨hlower n hn2, hn⟩

end Erdos790
