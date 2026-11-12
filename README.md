# Erdős 790 — matching order

Private JSP-000649 submission draft prepared on 12 November 2026.

For every sufficiently large integer n, the largest universally guaranteed distinct-summand-free subset of an n-element integer set has order

\[
  l(n)=\Theta\!\left(\frac{n}{(\log n)^2}\right).
\]

The new contribution supplies the matching upper bound. Samuel Korsky proved the lower bound and retains that mathematical credit. The complete argument appears in [the manuscript](paper/erdos790.md). The original problem is [Erdős 790](https://www.erdosproblems.com/790).

## Contributors

**Ghuffy1** is the repository owner and principal submitter. **Ghuffy1, JENW1N, H0W4RD-dev and lkruer** receive equal contribution credit under the owner's requested designation. Individual contributor confirmations and role-specific evidence remain in the private release checklist. Equal contribution credit does not specify a prize-payment arrangement.

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
lake exe cache get
lake --no-cache build Erdos790 Erdos790JSP
lake --no-cache build +Erdos790.Audit +Erdos790JSP.Audit
lake env lean Erdos790/Upper/Full.lean
lake env lean Erdos790JSP/StatementBridge.lean
lake env lean Erdos790JSP/Audit.lean
lake env leanchecker --fresh Erdos790JSP.StatementBridge
```

`cache get` retrieves the pinned library cache. The subsequent commands build the local sources. A fresh source-only reproduction can omit the first command, at a greater build cost. The final command replays the imported closure using Lean's kernel. It uses the same kernel implementation as Lean.

The declared proof and bridge targets must report only `propext`, `Classical.choice` and `Quot.sound` in their axiom dependencies. Actual commands, outcomes, cache provenance and limitations appear in [the verification report](verification/REPORT.md). Instructions are distinct from completed checks.

## Submission status

JSP-000649 follows the legacy process. The checked official catalog currently records Open, Lean proof No and Eligible to claim No. A complete result can be submitted for review. Official mathematical acceptance, Lean acceptance, priority adjudication and award eligibility remain pending. [Pinned rules](submission/RULES.md)

The intended remote is `Ghuffy1/erdos790-jsp`, branch `main`. This name is a preparation choice. A remote repository and public branch have not been created. The [PR draft](submission/PR_DRAFT.md) and [catalog patch](submission/catalog.patch) are prepared for a later authorized publication. The selected local proof commit and evidence commit are recorded separately.

## License and provenance

[LICENSE.md](LICENSE.md) identifies rights by source. The owner reports authorization for the adapted JENW1N/lkruer lower-bound files, with the grant or confirmation still to be supplied before public distribution. Preserve the Apache licenses for OpenAI and Kneser sources and the original source headers. All imported source bytes have a [SHA-256 manifest](provenance/source-files.json).
