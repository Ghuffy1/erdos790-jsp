# JSP rule and eligibility review

Reviewed on 12 November 2026 against the official awards repository at `b1bfe454d37db2838ef76756830aeb23c40de95e`, together with the live selection rules, claim pages and FAQ. The local package is a private draft. Official acceptance and award eligibility have not been granted.

## Eligibility assessment

**The full matching-order result has a complete-solution submission path for JSP-000649 under the legacy process.** It closes the catalog's extremal-order question using the new upper bound and Korsky's credited lower bound. The current entry is Open, Lean proof No and Eligible to claim No, with both claim roles Unavailable. JSP-000649 is absent from the 50-problem MathDB pilot. [Catalog](https://github.com/TheJustinSunPrize/awards/blob/b1bfe454d37db2838ef76756830aeb23c40de95e/problems/catalog-0601-0700.md#JSP-000649), [pilot register](https://github.com/TheJustinSunPrize/awards/blob/b1bfe454d37db2838ef76756830aeb23c40de95e/problems/mathdb-pilot.md)

The completed proof and formalization are dated in 2026, within the published achievement-date window beginning 1 January 2026. The committee must verify the evidence and decide mathematical scope, attribution, priority and award tier. No fixed award amount for this entry was found. [Selection rules](https://www.hejustinsun.com/prize/rules)

The complete manuscript and Lean formalization may be submitted together. A prior journal publication is not a stated entry prerequisite. Publication venue and academic recognition are evaluation factors for the committee's tier and allocation decision. [Selection rules](https://www.hejustinsun.com/prize/rules), [contribution procedure](https://github.com/TheJustinSunPrize/awards/blob/b1bfe454d37db2838ef76756830aeb23c40de95e/CONTRIBUTING.md)

## Requirements and preparation

| Requirement | Prepared evidence | Remaining action |
| --- | --- | --- |
| Complete original mathematical solution | `paper/erdos790.md`, complete matching-order theorem and all host sizes eventually | Official mathematical review |
| Full Lean proof and statement correspondence | Original source, independent statement and named equivalence bridge | Official Lean reproduction and acceptance |
| Exact proof revision in a named branch | `submission/SOURCE.json`, selected local commit in `main` | Publish the selected history when authorized and verify the public branch membership |
| Original contributor-owned repository | Proposed `Ghuffy1/erdos790-jsp`, new upper source with complete provenance | Create public source only after authorization; resolve other contributors' Lean ownership route |
| Exact toolchain and dependencies | `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, dependency and source manifests | Follow reproduction commands at the selected commit |
| Axiom results for targets | `Erdos790JSP/Audit.lean`, verification report and logs | Maintainer verification is separate |
| Mathematical and Lean roles identified separately | `CREDITS.md`, PR draft and source provenance | Obtain individual role confirmations and corroborating authorship evidence |
| Third-party rights and notices | Per-source license table and retained Apache licenses/headers | Obtain the reported lower-source grant and confirm new-source release licensing |
| Catalog-only official PR | `submission/catalog.patch`, generated against the pinned base | Rebase/check against the live catalog immediately before an authorized PR |
| Existing overlapping records disclosed | `submission/PRIORITY.md` and PR draft | Check new activity immediately before release |
| Public priority corroboration | Private source/proof hashes and dated checks | Add independently checkable public history at authorized release; private dates alone do not establish JSP priority |
| Own-account claims | Separate claim drafts and private checklist | Each claimant handles their own claim after the required acceptance/merge |
| Candidate public notice | Official register pending | Maintainers publish each role's candidate and allow 14 full days |
| Identity and recipient confirmation | Private checklist only | Each applicant sends the required private identity email and completes written recipient confirmation |

The optional self-check procedure is recorded separately from mandatory submission requirements. A technical self-check does not determine mathematical or Lean priority, identity, entitlement or payout. [Contribution rules](https://github.com/TheJustinSunPrize/awards/blob/b1bfe454d37db2838ef76756830aeb23c40de95e/CONTRIBUTING.md), [verification guidance](https://github.com/TheJustinSunPrize/awards/blob/b1bfe454d37db2838ef76756830aeb23c40de95e/docs/verification.md)

## Roles, ownership and equal contribution

Ghuffy1 is the designated repository owner and principal submitter. Ghuffy1, JENW1N, H0W4RD-dev and lkruer receive equal contribution credit in this draft. This records the owner's requested attribution, while individual confirmations and evidence for each claimed role remain pending.

Legacy Lean claims require the applicant's original personal repository or an organization repository with verifiable contribution evidence. Ghuffy1's personal ownership meets the owner condition for Ghuffy1. The other contributors' intended Lean claims need a maintainer-accepted ownership path. An original team organization administered by Ghuffy1 is an expressly documented option. The private draft preserves the requested owner while this claim-stage issue remains open. [Attribution requirements](https://github.com/TheJustinSunPrize/awards/blob/b1bfe454d37db2838ef76756830aeb23c40de95e/docs/attribution.md)

The published legacy split is 70% for the mathematical-solver role and 30% for the Lean-formalization role. A single entity doing both can receive the combined allocation. Teams designate an authorized representative and legal payee. Equal contribution credit does not supply a signed distribution agreement or authorize proxy claims. The current claim process requires each applicant to act for their own contribution. [Selection rules](https://www.hejustinsun.com/prize/rules), [legacy award process](https://github.com/TheJustinSunPrize/awards/blob/b1bfe454d37db2838ef76756830aeb23c40de95e/docs/award-process.md)

Korsky retains the lower-bound mathematics. HongJin HE retains the earlier lower-bound formalization record. JENW1N and lkruer retain their independently developed imported lower formalization. Those records must accompany review of the new upper-bound synthesis and full-result formalization. The committee determines how prior and new contributions affect award credit.

## Priority and completion of the claim process

Priority uses the selected complete proof and independently checkable history. A PR's opening time and an uncorroborated Git timestamp are insufficient. The full upper-bound contribution must be compared on its actual scope. The current searches found no earlier matching upper estimate, while private or unindexed work remains beyond a public search's reach. [Priority rules](https://github.com/TheJustinSunPrize/awards/blob/b1bfe454d37db2838ef76756830aeb23c40de95e/docs/award-process.md#lean-formalization-or-both-roles)

Future public steps are contribution submission, separate mathematical and Lean acceptance, merge where required, maintainer eligibility reconciliation, publication of role-specific candidates, 14 full days of public notice, resolution of relevant disputes and pending reviews, identity verification and written recipient confirmation. Public notice begins when a candidate actually enters the public register. Submission, merge or passage of time alone is insufficient. [Legacy award process](https://github.com/TheJustinSunPrize/awards/blob/b1bfe454d37db2838ef76756830aeb23c40de95e/docs/award-process.md)

## Official wording differences

The website describes some Lean-only identity exemptions and associates parts of the notice process with merge. The current operational repository requires an identity email from every applicant and starts notice at candidate publication. The website mentions partial-progress award tiers, while current contribution rules accept complete original-problem submissions. The website describes a Lean-containing PR, while the operational contribution rules require external proof sources and reference-only catalog changes. This draft follows the more precise current operational workflow and records these differences for reviewer confirmation. [FAQ](https://www.hejustinsun.com/prize/faq), [claim form](https://github.com/TheJustinSunPrize/awards/blob/b1bfe454d37db2838ef76756830aeb23c40de95e/.github/ISSUE_TEMPLATE/claim-award.yml)
