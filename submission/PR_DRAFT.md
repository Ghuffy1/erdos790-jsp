# Complete matching-order proof for JSP-000649 (Erdős 790)

Private, unsubmitted draft. The referenced remote is proposed and has not been created. Public links become usable only after authorized publication. Contributor-role confirmations and release rights remain recorded in the private checklist.

## Submission type

- [x] Mathematical solver information
- [x] Lean proof or formalization author information

This is a legacy-process contribution for JSP-000649, which is outside the MathDB pilot.

## Problem

- Problem ID JSP-000649, corresponding to Erdős 790.
- Original source is Erdős 790 and the cited 1973 formulation at printed page 130. [Original statement](https://www.erdosproblems.com/790), [1973 source](https://www.renyi.hu/~p_erdos/1973-21.pdf)
- Current entry is Open / Lean No / Eligible No. The proposed catalog change records a complete matching-order result, its full formalization, source and credits. Maintainers determine acceptance and reconcile eligibility and the index.
- Related records are PR 4701, withdrawn claim 4702, and scope request 4923. They concern Korsky's lower bound and its subsidiary answers. This contribution adds the matching upper bound. Earlier scoped or mismapped PRs 894, 2346 and 3399 are discussed in the priority review. [Priority review](https://github.com/Ghuffy1/erdos790-jsp/blob/22cf5480ffb8aaa9c0f3443c9c0a8457fe8285ab/submission/PRIORITY.md)
- The mathematical manuscript is *Matching order for Erdős problem 790*, private draft dated 12 November 2026, Theorem 1 and proof in Sections 1–5, with subsidiary conclusions in Corollary 2. The new upper construction combines with Korsky's credited lower bound. [Manuscript](https://github.com/Ghuffy1/erdos790-jsp/blob/0a69771b18df655fe47af2d5fb78a7d125fcd5f0/paper/erdos790.md)

## Formal statement

- Complete mathematical solution is supplied by the manuscript linked above.
- Mathematical review status is internally checked, with a completed Lean formalization. External specialist and JSP review are pending.
- Independent statement is in `Erdos790JSP/OriginalStatement.lean`; full proof targets are `Erdos790.matching_upper_bound`, `Erdos790.matching_order` and `Erdos790JSP.matching_order`. [Statement](https://github.com/Ghuffy1/erdos790-jsp/blob/0a69771b18df655fe47af2d5fb78a7d125fcd5f0/Erdos790JSP/OriginalStatement.lean), [main proof](https://github.com/Ghuffy1/erdos790-jsp/blob/0a69771b18df655fe47af2d5fb78a7d125fcd5f0/Erdos790/Upper/Full.lean), [bridge](https://github.com/Ghuffy1/erdos790-jsp/blob/0a69771b18df655fe47af2d5fb78a7d125fcd5f0/Erdos790JSP/StatementBridge.lean)
- Statement origin is a proposed independently formulated statement of the cited original, requiring maintainer review. No maintainer-approved challenge is being claimed.
- Finite sets range over all integers. Finset summands are pairwise distinct, exclude the head, and number at least two. The extremal function is the maximal guarantee for every host of the prescribed size. Positive absolute lower and upper constants apply to every sufficiently large natural-number size. Both subsidiary questions are included. The bridge proves equivalence of independently stated safety and guarantee predicates, then equality of the extremal functions. [Coverage matrix](https://github.com/Ghuffy1/erdos790-jsp/blob/0a69771b18df655fe47af2d5fb78a7d125fcd5f0/verification/STATEMENT.md)

## Proof submission

The proposed original repository contains the new upper-bound development, explicit imported-source attribution, the full proof and the independent statement bridge. Ghuffy1 is the owner and principal submitter.

```json
[
  {
    "repository": "https://github.com/Ghuffy1/erdos790-jsp",
    "branch": "main",
    "commit": "0a69771b18df655fe47af2d5fb78a7d125fcd5f0"
  }
]
```

- Proof entry `Erdos790/Upper/Full.lean`, theorem `Erdos790.matching_order`.
- Independent statement transfer `Erdos790JSP/StatementBridge.lean`, theorem `Erdos790JSP.matching_order`.
- The quantified progression input is discharged by the pinned OAI theorem. The upper construction, exact-size transfer and distinct-summand lift are proved in `Erdos790/Upper`. The lower result is the credited theorem `Erdos790.korsky`.

## Reproduction

- Exact toolchain `leanprover/lean4:v4.34.1`, from `lean-toolchain`.
- Mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612`; every transitive package is fixed in `lake-manifest.json`.
- Vendored OAI source revision `4eaee87548250b2682affda7d05d947c05554bae`, with the full transitive source closure and retained Apache license.
- Build instructions are pinned in the selected source revision. [README](https://github.com/Ghuffy1/erdos790-jsp/blob/0a69771b18df655fe47af2d5fb78a7d125fcd5f0/README.md), [dependency record](https://github.com/Ghuffy1/erdos790-jsp/blob/0a69771b18df655fe47af2d5fb78a7d125fcd5f0/provenance/dependencies.json)

```sh
lake --no-cache build Erdos790 Erdos790JSP
lake --no-cache build +Erdos790.Audit +Erdos790JSP.Audit
lake env lean Erdos790/Upper/Full.lean
lake env lean Erdos790JSP/StatementBridge.lean
lake env lean Erdos790JSP/Audit.lean
lake env leanchecker --fresh Erdos790JSP.StatementBridge
```

The named target audit prints complete declarations and transitive axiom sets. Actual outcomes and any reproduction limitations are in the verification report. The only permitted foundations for the stated targets are `propext`, `Classical.choice` and `Quot.sound`. [Audit source](https://github.com/Ghuffy1/erdos790-jsp/blob/0a69771b18df655fe47af2d5fb78a7d125fcd5f0/Erdos790JSP/Audit.lean)

## Pre-submission Lean verification

The local Windows build and all 18 direct target/axiom checks using the shared verification helper passed. The additional fresh whole-closure kernel replay timed out after 1200 seconds, and a full isolated reproduction is outstanding after WSL startup failure. The private self-check uses the official lean-verify guidance at awards revision `b1bfe454d37db2838ef76756830aeb23c40de95e`. This optional report records the selected proof commit `0a69771b18df655fe47af2d5fb78a7d125fcd5f0`, actual toolchain, source hashes, dependency pins, separate original-statement checks, axiom output, kernel replay and any limitations. Evidence is added in a later commit while the selected proof revision remains fixed. [Verification report](https://github.com/Ghuffy1/erdos790-jsp/blob/22cf5480ffb8aaa9c0f3443c9c0a8457fe8285ab/verification/REPORT.md), [target manifest](https://github.com/Ghuffy1/erdos790-jsp/blob/22cf5480ffb8aaa9c0f3443c9c0a8457fe8285ab/verification/targets.json)

## Attribution

The submitting contributors have a potential award interest. Each future applicant must claim their own contribution through the applicable process.

- Proposed submission contributors are **Ghuffy1, JENW1N, H0W4RD-dev and lkruer**, with equal contribution credit, and **Ghuffy1** as owner and principal submitter. Individual role confirmations and supporting public authorship evidence must be supplied before asserting each person's claim entitlement.
- **Samuel Korsky** retains mathematical authorship of the lower estimate. His prior subsidiary consequences are expressly credited. **Jensen Kohlmeyer (JENW1N)** and **Liam Kruer (lkruer)** retain authorship of the imported lower formalization, prepared with Claude assistance.
- **HongJin HE** retains the earlier public lower-result formalization record. This submission claims the new matching upper bound and full-order synthesis.
- Imported Kneser code credits **Mantas Bakšys and Yaël Dillies**. The OAI formalization, **Kelley–Meka** input and underlying library authors are credited with exact source pins.
- Internal reviews and Codex-assisted formalization are disclosed. No external human verifier, official acceptance or unconditional first priority is claimed.
- Public authorship evidence for the new work is pending authorized release. Local private completion evidence is preserved. Repository ownership and commit author identity alone supply no authorship proof. [Full credits](https://github.com/Ghuffy1/erdos790-jsp/blob/0a69771b18df655fe47af2d5fb78a7d125fcd5f0/CREDITS.md)

## Submission checklist

- [ ] The final public PR changes only permitted catalog attribution, Lean/source and publication fields.
- [x] The submitted result fully solves the original problem and the selected Lean proof is complete, with no `sorry`, `admit` or added unproved assumptions replacing proof steps.
- [x] The mathematical proof, statement correspondence, source pins, build commands and prior mathematical/formalization roles are supplied in this draft.
- [ ] Every claimed role has confirmed authorship, rights and sufficient public contribution evidence; the source is publicly available in the named branch at the selected full SHA.
- [ ] The final awards PR contains no proof source, dependencies, archives, binaries or private identity/contact/payment information.

Unchecked items are future submission or review conditions. The local draft has not been posted.
