import OAI.Combinatorics.Progressions.Results.Conclusions
import Erdos790.Upper.WitnessConstruction

/-!
# Matching order for Erdős problem 790

Samuel Korsky proved the lower bound. The new upper construction is developed
in the `Erdos790.Upper` modules. Its progression input uses the pinned OpenAI
formalization of a quantitative density theorem, whose three-term consequence
is sufficient here. Kelley–Meka's quantitative three-term progression theorem
is the mathematical input cited by the original upper-bound manuscript.

The source revisions and the credits for the lower-bound formalization and
the Kneser theorem are recorded in the private project's provenance documents.
-/

namespace Erdos790

theorem matching_upper_bound : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ n : ℕ in Filter.atTop, (l n : ℝ) ≤ C * n / Real.log n ^ 2 :=
  Upper.eventual_upper_from_quantitative
    (OAI.Erdos3.manuscriptQuantitativeDensityTheorem 3 (by decide))

theorem matching_order : MatchingOrder :=
  matchingOrder_of_eventual_upper matching_upper_bound

end Erdos790
