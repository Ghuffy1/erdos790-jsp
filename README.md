# Erdős 790 — matching order

JSP-000649 submission prepared on 12 November 2026 and released by Ghuffy1.

For every sufficiently large integer n, the largest universally guaranteed distinct-summand-free subset of an n-element integer set has order

\[
  l(n)=\Theta\!\left(\frac{n}{(\log n)^2}\right).
\]

The new contribution supplies the matching upper bound. Samuel Korsky proved the lower bound and retains that mathematical credit. The complete argument appears in [the manuscript](paper/erdos790.md). The original problem is [Erdős 790](https://www.erdosproblems.com/790).

## Contributors

**Ghuffy1** is the repository owner and principal submitter. **Ghuffy1, JENW1N, H0W4RD-dev and lkruer** receive equal contribution credit under the owner's requested designation. Individual contributor roles and supporting evidence remain subject to attribution review. Equal contribution credit does not specify a prize-payment arrangement.

Historical mathematics, imported formalizations and AI assistance are identified in [CREDITS.md](CREDITS.md). This repository contains original upper-bound formalization together with explicitly attributed dependency sources. The lower-bound formalization retains its prior authorship.

## Main declarations

| Declaration | Content |
| --- | --- |
| `Erdos790.matching_upper_bound` | Eventual upper bound with an absolute positive constant |
| `Erdos790.matching_order` | Complete two-sided matching-order estimate |
| `Erdos790.korsky` | Korsky's lower estimate for all n ≥ 2 |
| `Erdos790.erdos_790_part_i` | l(n)/√n tends to infinity |
| `Erdos790.erdos_790_part_ii` | No eventual fixed power-saving upper bound |
| `Erdos790.erdos_790_exponent` | log(l(n))/log(n) tends to 1 |
| `Erdos790JSP.matching_order` | Transfer to the independently stated original problem |

`Erdos790.IsSumFree` forbids a head equal to a sum of at least two distinct other elements. `Erdos790JSP/OriginalStatement.lean` gives an independent formulation using finite subsets and exclusion of the head. [Statement correspondence](verification/STATEMENT.md) details the bridge and the quantifiers.

## Reproduce

Use `leanprover/lean4:v4.34.1`, pinned in `lean-toolchain`. Mathlib and all transitive package revisions are fixed in `lake-manifest.json`. The vendored OpenAI source is pinned separately in [the dependency manifest](provenance/dependencies.json).

After checking out the selected proof commit from `submission/SOURCE.json`, run from the repository root.

```sh
lake --no-cache build Erdos790 Erdos790JSP
lake --no-cache build +Erdos790.Audit +Erdos790JSP.Audit
lake env lean Erdos790/Upper/Full.lean
lake env lean Erdos790JSP/StatementBridge.lean
lake env lean Erdos790JSP/Audit.lean
lake env leanchecker --fresh Erdos790JSP.StatementBridge
```

These commands build the sources at the pinned revisions. Compatible existing dependency outputs can be reused after checking their source and toolchain identities. Any optional Mathlib cache fetch should be scoped to the imports needed by the proof. The final command replays the imported closure using Lean's kernel. It uses the same kernel implementation as Lean.

The declared proof and bridge targets must report only `propext`, `Classical.choice` and `Quot.sound` in their axiom dependencies. Actual commands, outcomes, cache provenance and limitations appear in [the verification report](verification/REPORT.md). The local Windows build and all 18 target axiom checks passed. The additional fresh whole-closure kernel replay timed out at its 1200-second limit. The full isolated reproduction remains outstanding after WSL startup failure. The report records these completed and incomplete levels.

## Submission status

JSP-000649 follows the legacy process. The checked official catalog currently records Open, Lean proof No and Eligible to claim No. A complete result can be submitted for review. Official mathematical acceptance, Lean acceptance, priority adjudication and award eligibility remain pending. [Pinned rules](submission/RULES.md)

The original source repository is [Ghuffy1/erdos790-jsp](https://github.com/Ghuffy1/erdos790-jsp), branch `main`. The catalog contribution is submitted as [JSP pull request 5573](https://github.com/TheJustinSunPrize/awards/pull/5573) and awaits official review. The [submission text](submission/PR_DRAFT.md) and [catalog patch](submission/catalog.patch) accompany the JSP contribution. The selected proof commit and verification-evidence commit are recorded separately in [SOURCE.json](submission/SOURCE.json).

## License and provenance

[LICENSE.md](LICENSE.md) identifies rights by source. Ghuffy1 confirms authorization to redistribute the adapted JENW1N/lkruer lower-bound files. Further written confirmation and its precise scope can be supplied for rights review. Preserve the Apache licenses for OpenAI and Kneser sources and the original source headers. All imported source bytes have a [SHA-256 manifest](provenance/source-files.json).
