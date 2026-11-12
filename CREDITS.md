# Credits and contribution record

## Submission contributors

The owner has designated **Ghuffy1, JENW1N, H0W4RD-dev and lkruer** as equal contributors to the full-result submission. **Ghuffy1** is the owner and principal submitter. This designation records the owner's instructions. Individual confirmation, the evidence for each mathematical or formalization role, and any representative or payment agreement require separate documentation.

The new upper argument originated in a private multi-agent research session and was formalized with Codex assistance. Internal mathematical reviews and the reproducible Lean verification support the result. These reviews are team-internal and machine-assisted. No external specialist or JSP acceptance is asserted. No historical coauthor commits or signatures have been manufactured.

## Lower bound and earlier questions

**Samuel Korsky** proved the lower bound of order n/(log n)² in *Large Sum-Free Subsets of Sets of Integers*, Theorem 1, dated 13 September 2026. Korsky attributes the main bisection-list idea to GPT Astra and states that he completed and verified the proof. The present synthesis uses this result with credit. Its subsidiary asymptotic consequences are earlier results. [Public claim and manuscript](https://www.erdosproblems.com/forum/thread/790/proof-claims)

The imported lower-bound Lean files are the formalization by **Jensen Kohlmeyer (JENW1N)** and **Liam Kruer (lkruer)**, prepared with Claude assistance, at revision `ca7ef62267bb255b709fb4b67caa7d8db4d9f248`. The files are `Erdos790/Defs.lean`, `Bisection.lean`, `Average.lean`, `Positive.lean`, `Main.lean`, `Sanity.lean` and `Check.lean`, where present in that source. File identities and later packaging changes are recorded in the provenance manifests. [Imported source](https://github.com/JENW1N/erdos790-lean/tree/ca7ef62267bb255b709fb4b67caa7d8db4d9f248)

**HongJin HE** has an earlier public formalization of Korsky's theorem and its consequences, at revision `afdea20c9e778d75173d8a13cf7e6548157386b6`, publicly recorded on 18 September 2026. Preserve that earlier formalization credit. [Earlier source](https://github.com/hongjin-he/erdos-lean/commit/afdea20c9e778d75173d8a13cf7e6548157386b6)

Choi, Komlós and Szemerédi supplied the earlier O(n/log n) upper estimate and a lower estimate already implying the square-root subsidiary answer. The manuscript identifies their place in the history.

## Imported mathematical infrastructure

The Kneser formalization credits **Mantas Bakšys and Yaël Dillies** and comes from `YaelDillies/misc-yd@f2f1d413b681dfd7a0f0e8481aee3ab7e0bae7ba`. Its original headers and Apache 2.0 license are retained. Local adaptation and import changes remain attributable to the present formalization. [Upstream](https://github.com/YaelDillies/misc-yd/tree/f2f1d413b681dfd7a0f0e8481aee3ab7e0bae7ba)

The quantitative progression theorem used by Lean is supplied by **OpenAI's mathematics development**, revision `4eaee87548250b2682affda7d05d947c05554bae`. All 4,136 Lean source files in its transitive source closure are included unchanged under `vendor/openai_math/lean`, with its Apache 2.0 license. Upstream per-file author notices remain intact. The new finite Varnavides and centered-pair bridge is in `Erdos790/Upper/ProgressionInput.lean`. [Pinned upstream](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae)

**Zander Kelley and Raghu Meka** provide the quantitative three-term progression theorem invoked by the informal manuscript. The Lean route uses the separately identified OAI density theorem. [Paper](https://arxiv.org/abs/2302.05537)

Lean, Mathlib and their dependencies retain their own licenses, authorship and exact pinned revisions. [Dependency manifest](provenance/dependencies.json)

## Priority

The recorded search found no earlier matching upper bound. The current work has private provenance and local completion evidence. Public corroboration of priority and JSP's role-specific priority decisions are pending. Repo ownership, upload time and equal contributor labels alone establish no historical priority.
