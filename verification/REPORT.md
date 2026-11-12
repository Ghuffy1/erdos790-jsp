# Verification passed at the local Lean level

The full integer-host matching-order theorem at private source commit `0a69771b18df655fe47af2d5fb78a7d125fcd5f0` passes the recorded local Lean build and all 18 source-level target/axiom checks. The additional fresh whole-closure kernel replay ended at its 1200-second limit with exit 124. Its completion is unverified. The independently stated original problem is connected by proved definition and extremal-function equivalences. A complete isolated reproduction also remains outstanding after the WSL environment failed to start. JSP acceptance, authorship, priority and prize eligibility remain pending decisions.

## Explicit conclusions

1. **Does the proof address the specified original problem? Yes.** It covers arbitrary finite integer hosts, a separate head and at least two distinct summands, positive absolute constants and every sufficiently large natural cardinality.
2. **Did the specified commit pass local Lean compilation and target checks? Yes.** The normal source build and the complete source-level target/axiom batch using the shared verification helper exited zero. The additional fresh whole-closure replay timed out with exit 124, so that verification level remains incomplete.
3. **Does it fully solve the original problem? Yes, for the finite integer-host asymptotic-order question.** It proves l(n) = Θ(n/(log n)²) and includes both named subsidiary answers. The lower theorem retains Korsky's authorship.
4. **Does it meet the Lean completeness requirements? Meets within the stated Lean kernel trust scope.** The checked targets use only the three standard foundations, with no admitted proof step or extra mathematical hypothesis. Official review is pending.

## Pinned input and correspondence

The proposed remote is `Ghuffy1/erdos790-jsp`, branch `main`, and has not been created. The selected local commit is `0a69771b18df655fe47af2d5fb78a7d125fcd5f0`. The audited checkout was separate from the editable package, clean at preflight, and checked against 4,280 Lean source hashes. Every source hash matched. All nine actual dependency commits matched the manifest and their tracked source trees were clean. [Source check](package-check.json), [dependencies](dependencies.json), [target manifest](targets.json), [preflight](preflight.json)

The original statement and its complete coverage matrix are in `STATEMENT.md`. The independent `Erdos790Original.Safe` uses a finite subset and explicit exclusion of the head. `safe_iff`, `guaranteed_iff` and `extremal_eq` establish equivalence to the submitted definitions before transferring the result. The theorem `Erdos790.matching_order` has no progression-bound premise. `Full.lean` supplies the OAI theorem that discharges that input.

The manuscript distinguishes its informal Kelley–Meka route from the formal OAI quantitative-density route, and makes the largest-differing-digit convention explicit. Internal independent scope reviews found no definition or quantifier gap. They were team-internal and machine-assisted.

## Reproduction and completed levels

The final complete checks used Windows Lean 4.34.1, compiler commit `5045d0056413266e57c625dcd7c365b10e377c52`, with Lake 5.0.0 from the same distribution. Runtime binary hashes are recorded in `dependencies.json`. Commands, dates, exits, durations and log hashes are in `results.json`. Local path prefixes are normalized to documented placeholders in public evidence. Raw logs and their original hashes remain private.

| Placeholder | Meaning |
| --- | --- |
| `${PROJECT}` | Clean checkout of the selected source commit |
| `${LEAN_TOOLCHAIN}` | Verified Lean 4.34.1 distribution |
| `${PACKAGES}` | The nine dependency checkouts at the recorded Git revisions |
| `${BUILD}` | Compiled outputs corresponding to the selected project sources |
| `${OAI_BUILD}` | Existing verified outputs for the pinned OAI source |
| `${VERIFY_LEAN_HELPER}` | The local shared verification helper identified below |

The README supplies equivalent reproduction commands using standard Lake and Lean. The local storage helper is a convenience of this verification environment.

- Normal `lake --no-cache build Erdos790 Erdos790JSP` completed successfully. Unchanged artifacts with checked source identities were reused, together with the recorded source elaborations.
- The recorded build sequence elaborated the exact selected sources of `Erdos790/Upper/Full.lean` and `Erdos790JSP/StatementBridge.lean`, with valid completed artifacts reused by the final normal build.
- `hub/verification_storage/verify_lean.py` directly elaborated `Erdos790JSP/Audit.lean` using the verified F-drive compiler and compatible existing library outputs. This source-level batch checks and prints all 18 listed target declarations and their transitive axiom dependencies. The official JSP helper supplied preflight and prepared harness checks. [Actual audit output](native-check-audit.log)
- `leanchecker --fresh -v Erdos790JSP.StatementBridge` attempts to replay all imported constants and bridge declarations into a fresh environment using Lean's kernel. It reached its 1200-second limit and was terminated with exit 124. Its log contains the termination receipt and supplies no completed replay verdict. This additional check remains incomplete. An independently implemented external kernel/comparator was not run.

An earlier isolated Linux execution used dedicated mount, network and PID namespaces, no credentials or user home, read-only source and toolchain mounts, and private output paths. It elaborated the selected revision's full theorem, including `Erdos790/Upper/Full.lean`, and its independent statement. Dependency-cache metadata used private copy-on-write layers. The WSL environment subsequently stopped and returned `Wsl/Service/CreateInstance/E_FAIL`, preventing completion of that isolated run. The completed build and target checks used the pinned Windows runtime with controlled search paths, one Lean thread and F-only project output. This was a host execution. Full security-isolated reproduction and an independent external kernel check remain outstanding for official verification.

## Cache and execution limitations

The unchanged 4,136-file OAI dependency closure reused artifacts from the earlier verified Lean 4.34.1 source build. That earlier build completed 13,200 jobs with exit zero and 249 named standard-axiom audits. Its raw log SHA-256 is `9704d0519003f678ec3f997c9d77f1d01ca6d829e837564ee603ce73ea8c6123`. Its full private receipt and raw log remain in the earlier review. This run independently checks source identities, the normal package build and fresh local elaboration. The attempted additional fresh kernel replay is incomplete. A second fully cold compilation of every upstream dependency remains unperformed.

Initial preparation runs exposed a dependency-package identity mismatch and attempts to refresh metadata in read-only caches. The portable package was corrected to retain `erdos790_dependency_check` as the upstream OAI package identity. The successful selected revision is the corrected commit identified above. An optional `--rehash` run was stopped during this diagnosis. The Linux preflight's initial Git-status scan exceeded the helper's 20-second limit. The unchanged official helper then completed preflight and preparation on the pinned clean checkout through the host's Git implementation. A separate freshness-only check requested object files for command-only audit modules and correctly reported that they required compilation. The subsequent direct source check through `verify_lean.py` supplies the actual audit evidence. Earlier diagnostic runs are retained privately. Imported sources emit non-failing deprecation/style warnings, which were preserved with their authorship.

## Target axiom results

| Declaration | Observed dependencies |
| --- | --- |
| `Erdos790.matching_upper_bound` | `Classical.choice`, `Quot.sound`, `propext` |
| `Erdos790.matching_order` | `Classical.choice`, `Quot.sound`, `propext` |
| `Erdos790.korsky` | `Classical.choice`, `Quot.sound`, `propext` |
| `Erdos790.erdos_790_part_i` | `Classical.choice`, `Quot.sound`, `propext` |
| `Erdos790.erdos_790_part_ii` | `Classical.choice`, `Quot.sound`, `propext` |
| `Erdos790.erdos_790_exponent` | `Classical.choice`, `Quot.sound`, `propext` |
| `Erdos790.erdos_790` | `Classical.choice`, `Quot.sound`, `propext` |
| `Erdos790.eventually_rpow_le_l` | `Classical.choice`, `Quot.sound`, `propext` |
| `Erdos790JSP.safe_iff` | `Classical.choice`, `Quot.sound`, `propext` |
| `Erdos790JSP.guaranteed_iff` | `Classical.choice`, `Quot.sound`, `propext` |
| `Erdos790JSP.extremal_eq` | `Classical.choice`, `Quot.sound`, `propext` |
| `Erdos790JSP.matching_order` | `Classical.choice`, `Quot.sound`, `propext` |
| `Erdos790JSP.upper_bound` | `Classical.choice`, `Quot.sound`, `propext` |
| `Erdos790JSP.lower_bound` | `Classical.choice`, `Quot.sound`, `propext` |
| `Erdos790JSP.first_question` | `Classical.choice`, `Quot.sound`, `propext` |
| `Erdos790JSP.second_question` | `Classical.choice`, `Quot.sound`, `propext` |
| `Erdos790JSP.exponent` | `Classical.choice`, `Quot.sound`, `propext` |
| `OAI.Erdos3.manuscriptQuantitativeDensityTheorem` | `Classical.choice`, `Quot.sound`, `propext` |

The allowed set is `propext`, `Classical.choice` and `Quot.sound`. These are standard classical Lean foundations. The target audit observed no `sorryAx`, added unproved hypothesis or native-computation trust axiom. Formal checks and interpretation of the original prose are complementary. [Audit output](native-check-audit.log)

## Prize and release status

This report verifies the stated mathematical/formal result. The entry remains officially Open / Lean No / Eligible No until JSP's review and record updates. The legacy submission path exists. The package retains the requested owner and equal-contribution designation, while individual contribution confirmations, the reported lower-source permission grant, public provenance and the source-ownership route for co-claimants remain release/claim items. [Rules review](../submission/RULES.md), [priority review](../submission/PRIORITY.md)

The public search found no earlier matching upper estimate. Worldwide first priority remains unverified. At the completion of these verification checks, this preparation was private. Ghuffy1 subsequently authorized public release on 12 November 2026. The recorded checks and their limitations apply to the unchanged selected proof commit.
