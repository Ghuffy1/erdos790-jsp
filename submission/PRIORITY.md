# Literature, related submissions and priority

The search supports an apparently new matching upper estimate for the full finite-host problem. It establishes no unconditional claim of first priority. The complete private search record predates this package and was refreshed on 12 November 2026.

## Scope and search coverage

The earlier review retained 74 public retrievals and 214 arXiv records with abstracts. It inspected original problem sources, the Choi–Komlós–Szemerédi paper, Korsky's manuscript, forward citations, bibliographic searches and theorem-level GitHub sources. Searches included the original paper titles, `Erdos790`, `erdos_790`, the distinct-other-summands condition and known logarithmic bounds. MathSciNet and zbMATH subscription coverage was unavailable. Public search also cannot exclude private manuscripts or unindexed work.

The latest refresh checked the official catalog, public scope and attribution discussions, current claim status and public searches for the problem and original titles. Only established public terminology was sent to search services. The private proof text was kept local.

The 12 November refresh also screened Jagannath Bhanja's 2026 *On the size and structure of certain subsequence sum set* through the publisher's abstract, introduction and displayed section results. Its extremal quantities count subsum sets and their minimizers in integers and finite cyclic groups. This inspection added no competing matching estimate for the guaranteed subset function l(n). [Publisher record](https://www.sciencedirect.com/science/article/abs/pii/S0012365X25005837)

## Prior mathematics

| Work | Relation to the full result |
| --- | --- |
| Erdős, 1965, printed page 188; 1973, printed page 130 | Original finite-host questions and early bounds |
| Choi, 1973; Cantor, 1974 | Earlier finite-host estimates |
| Choi, Komlós and Szemerédi, 1975 | O(n/log n) upper estimate and a lower estimate implying the square-root subsidiary answer |
| Korsky, 13 September 2026, Theorem 1 | Lower estimate Ω(n/log² n), settling the fixed-power question while leaving a logarithmic gap |
| Kelley–Meka and the pinned OAI development | Quantitative arithmetic-progression inputs, credited in the manuscript and formal dependency record |

No earlier matching O(n/log² n) upper estimate was located. The new contribution is the matching upper bound and resulting two-sided order. The new work depends on the credited prior lower bound.

Original and prior sources are linked in the manuscript. [Erdős 1973 source](https://www.renyi.hu/~p_erdos/1973-21.pdf), [Choi–Komlós–Szemerédi paper](https://www.ams.org/journals/tran/1975-212-00/S0002-9947-1975-0376594-1/), [Korsky claim and manuscript](https://www.erdosproblems.com/forum/thread/790/proof-claims)

## Public repositories and discussions

| Record | Reviewed scope |
| --- | --- |
| HongJin HE, `hongjin-he/erdos-lean@afdea20c9e778d75173d8a13cf7e6548157386b6` | Earlier public formalization of Korsky's lower result and consequences, recorded on 18 September 2026 |
| `JENW1N/erdos790-lean@44a5c97f66dd67cef224af0f51d04e0875e87202`, later revision `ca7ef62267bb255b709fb4b67caa7d8db4d9f248` | Independent lower-result formalization by Jensen Kohlmeyer and Liam Kruer; original selected proof public on 5 October 2026 |
| Awards PR 4701 | Open draft supporting-catalog update for the two subsidiary questions; expressly retains the broader problem's open status |
| Awards issue 4702 | Earlier JENW1N claim withdrawn from active award consideration; lower-result scope and earlier HongJin HE priority disclosed |
| Awards issue 4923 | Pending scope request for the separately posed subsidiary questions, including 790 |
| Awards PR 894 | Closed, unmerged interval construction, with no complete arbitrary-host solution claimed |
| Awards PR 2346 | Closed, unmerged scoped record with trivial target declarations |
| Awards PR 3399 | Closed, unmerged record mapping JSP-000649 to Erdős 649, a mismatched original problem |
| [`competemath/tengoku` at `13757ca5`](https://github.com/competemath/tengoku/blob/13757ca5ae136638242a2fe56387eda7ab7ef940/Tengoku/ErdosLean/ErdosLean/Erdos790/Statement.lean) | Recorded lower-result scope and remaining upper gap |
| [`google-deepmind/formal-conjectures` PR 7598](https://github.com/google-deepmind/formal-conjectures/pull/7598) | Statement work with placeholders at the inspected revision |
| [`ryantuck/erdos-ai` at `f5e45cc9`](https://github.com/ryantuck/erdos-ai/blob/f5e45cc97f93cd22802b2f1c37f08f0bf7becb86/deepmind/deepmind/790.lean) | Prior-bound statements and placeholders |
| [`rjwalters/lean-genius` at `d8540c5a`](https://github.com/rjwalters/lean-genius/blob/d8540c5a48f69a9f57b87c549c6e09dad63a0670/proofs/Proofs/Erdos790Problem.lean) | Axiomatized key statements did not supply the matching result |
| [`daedalus/alphaproof-nexus` at `4e65a6ca`](https://github.com/daedalus/alphaproof-nexus/blob/4e65a6ca81655f090a3c8dcf9f56e4a38c984f4c/problems/erdos/790/Erdos790.lean) | Empty theorem block |
| [`plasma-ai/erdos` at `b6f7945a`](https://github.com/plasma-ai/erdos/blob/b6f7945a32a8892757db3d84cde1e4b21e557ce4/wiki/problems/additive_combinatorics/E0790/_index.md) | Prior-bound catalog record |
| [`przchojecki/agentic-erdos` at `c58f8589`](https://github.com/przchojecki/agentic-erdos/blob/c58f8589136880d44f4a4299e5fc01fd5084506f/notes/ep790.md), [Problem a Day](https://www.erdosproblemaday.com/report/790) and [public Botnet record](https://botnet.com/topics/a76e0fdb-a165-44af-b2cf-9e03490c5dd2) | Catalog information or finite/square-root partial work at inspected revisions |
| `openai/math@4eaee87548250b2682affda7d05d947c05554bae` | Source of the progression input; its publication and preprint indexes did not contain an Erdős 790 matching-order result |

A previously cited number 4610 returned HTTP 404 in the present awards refresh and supplies no current priority evidence. The missing record is retained as a search limitation. The source review also screened work on ordinary three-term sum-free sets and infinite sequences to ensure the finite arbitrary-length distinct-summand condition matched.

[PR 4701](https://github.com/TheJustinSunPrize/awards/pull/4701), [withdrawn claim 4702](https://github.com/TheJustinSunPrize/awards/issues/4702), [scope request 4923](https://github.com/TheJustinSunPrize/awards/issues/4923), [PR 894](https://github.com/TheJustinSunPrize/awards/pull/894), [PR 2346](https://github.com/TheJustinSunPrize/awards/pull/2346), [PR 3399](https://github.com/TheJustinSunPrize/awards/pull/3399)

## Outstanding priority evidence

The new complete upper proof and formalization have private dated provenance. The selected local Git commit records the packaged source at its actual preparation time. Neither fact alone provides the independently checkable public chronology required by JSP. Publication and the associated public history await the owner's instruction.

JSP assesses mathematical priority and Lean priority separately. Earlier lower-bound formalizations cannot be treated as a newly established first formalization by this submission. The scope of the new full-order result, its original upper-bound formalization and all earlier contributions must be presented together for official attribution review.
