# Original statement and coverage

The target is the finite integer-set problem in Erdős 790 and JSP-000649. For a finite integer set B, exclude every equation b₀ = b₁ + ⋯ + bᵣ with r ≥ 2 and all participating elements distinct. Let l(n) be the largest size guaranteed in every n-element integer host.

| Original obligation | Formal evidence | Coverage |
| --- | --- | --- |
| Arbitrary finite integer hosts, including zero and negative elements | `Erdos790Original.Guaranteed`, `Erdos790.admissible` and `guaranteed_iff` | Full |
| All summands pairwise distinct and separate from the head | Finset summands in `Safe`, with `b ∉ S`; proved equivalent to `S ⊆ B.erase b` by `safe_iff` | Full |
| At least two summands | `2 ≤ S.card` in both definitions | Full |
| Genuine maximal universal guarantee | Natural-number supremum, original `l_spec`, `le_l`, `bddAbove_admissible` and `extremal_eq` | Full |
| Positive absolute lower and upper constants | `Erdos790.matching_order`, transferred to `Erdos790JSP.matching_order` | Full |
| Every sufficiently large cardinality | `∀ᶠ n : ℕ in atTop`, with exact-size packing in the upper proof | Full |
| Square-root ratio tends to infinity | `Erdos790.erdos_790_part_i`, `Erdos790JSP.first_question` | Full |
| No eventual fixed power-saving upper bound | `Erdos790.erdos_790_part_ii`, `Erdos790JSP.second_question` | Full |
| Stated exponent corollary | `Erdos790.erdos_790_exponent`, `Erdos790JSP.exponent` | Full |
| No extra quantitative-progression assumption | `Full.lean` instantiates the input with the pinned OAI theorem | Full |

The independent statement module imports trusted Mathlib modules and no `Erdos790` definitions. The bridge first proves equivalence of the finite-set properties and universal guarantees. Equality of the extremal functions then transfers the conclusions. This checks a precise independent statement. Human mathematical interpretation is still required to relate either formal statement to the original prose.

Positive integer witness sets suffice for the upper estimate because they belong to the unrestricted integer-host class. The lower theorem covers the unrestricted class by reduction to a nonzero sign class. The formal target is the integer-host catalog statement. The older real-host formulation is treated in the mathematical lower-bound literature, and no additional real-host Lean theorem is claimed here.

The earlier theorem `Erdos790.erdos_790` answers the two subsidiary questions. The full order is proved by `Erdos790.matching_order` in `Erdos790/Upper/Full.lean`. The target names have separate scopes.

The informal final lift cites Kelley–Meka supersaturation. The Lean proof uses OAI's quantitative progression-free density theorem and proves its own finite centered-pair bridge. The supplied manuscript records both sufficient inputs explicitly.

Original source locations are Erdős problem 790, the 1973 formulation cited there at printed page 130, and the JSP-000649 catalog statement. [Original problem](https://www.erdosproblems.com/790), [1973 source](https://www.renyi.hu/~p_erdos/1973-21.pdf), [pinned catalog](https://github.com/TheJustinSunPrize/awards/blob/b1bfe454d37db2838ef76756830aeb23c40de95e/problems/catalog-0601-0700.md#JSP-000649)
