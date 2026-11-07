# CHECKS-PALOMAR — the record of the checks on the Palomar packaging (2026-11-07)

Every check below ran on commit `ccd8a779052edfd828fa575ae03fd82d9a9d1e81` of this branch. The commit that adds this
file changes no `.lean` file, no Lake file and not `comparator.json`; besides this file it corrects one sentence of
`NOTICE` and one of `formalization.yaml` (`git diff --stat ccd8a779 HEAD` shows it), and the licence and metadata
checks were run again on it (below). The record clone was made fresh from a git bundle on a RunPod CPU
machine (8 vCPU, 64 GB cgroup memory limit, Ubuntu 24.04.3 LTS, Linux 6.8, x86_64, Python 3.12.3, Ruby 3.2.3), every
process under `taskset` on the container's eight CPUs. Toolchain: Lean v4.35.0-rc2
(`11acb17ec6b07a8f9e9173e6845197929540936b`), Lake 5.0.0-src+11acb17, installed by elan 4.2.4; Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55` and its eight pinned dependencies from `lake-manifest.json`, built output
by `lake exe cache get` into an empty `.lake`. Nothing was reused from earlier runs except the installed toolchain.
Wall clock and maxRSS come from `/usr/bin/time -v`; maxRSS is its "Maximum resident set size" in KiB, written here as
GB = KiB ÷ 10⁶. The record run took 15 min 52 s (20:56:57 Z to 21:12:49 Z); `leanchecker --fresh` ran after it, alone. Raw
logs are kept outside the repository.

## The sandbox: what could not run here, and what ran instead

`lake comparator` builds and exports the project, and runs the kernels, inside a `bwrap` sandbox. On this machine
`bwrap` cannot start: the container runs in a user namespace (uid 0 is mapped to 655360), the host restricts
unprivileged user namespaces (`kernel.apparmor_restrict_unprivileged_userns = 1`) and `/proc/sys` is read-only, so
`bwrap` stops with "No permissions to create new namespace". The disabling flag (`--inadvisably-no-sandbox`) was not
used. So **`scripts/verify-comparator.sh` (PalomarTemplate's, as Palomar runs it) did not reach a verdict here**: it
exits 1 at its first sandboxed step. What ran instead, step by step, is the same judgement:

1. **Exports.** The toolchain's own exporter, `lake env leanexport <module> -- <names>`, run on Challenge and on
   Solution with exactly the declarations `lake comparator` asks it for (Lake's `Check.lean`, `compareIt`: the
   builtin targets `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`, the four theorem names, the three permitted axioms,
   and the 28 primitive targets `Nat.add` … `outParam`).
2. **The comparison and the axiom check**, by `lake comparator --challenge-from-export … --solution-from-export …`,
   which runs them in its own process (`compareAt`: every compared statement equal, and every constant those
   statements reach equal in both exports; `checkAxioms`: no axiom outside the three) and only then spawns the
   kernels, in the sandbox. It passed both and stopped at the first kernel spawn ("Running Lean default kernel on
   solution", then the `bwrap` error), exit 1. The six negative controls below are refused by these two stages, with
   the messages they print, so the stages are not vacuous.
3. **The kernels**, run directly on the same Solution export with the same binaries and arguments as
   `runKernels` / `bundledKernels` (Lean's `leanchecker --silent --from-export`, and with `--paranoid` also
   `leanchecker-paranoid`, `lean4lean --import`, `nanoda_bin <config>` with the configuration Lake writes,
   `con-leche`, `con-ron`; `con-ron --jobs=2` as Palomar's records show), outside the sandbox. All six accept; on a
   forged export all six reject.

The sandbox guards the judge against adversarial code in the project; here the project is this repository's own.
Palomar's verifier runs the sandboxed path itself; it has not been run on this commit.

## The table

| check | tool + version | verdict | exit | wall | maxRSS |
|---|---|---|---|---|---|
| source rules | `scripts/check-lean-sources.py` (PalomarTemplate `2891de4c`, unmodified) | **pass**: all 36 `.lean` files start with `module`, none over 10,000 lines | 0 | 0.03 s | — |
| Challenge size | `wc` | 100 lines, 5,712 bytes (limits 1,000 / 100 KiB; preferred 300 / 32 KiB); imports only `Mathlib` | — | — | — |
| verbatim, formal-conjectures | `checks/verbatim_palomar.py <174.lean @ 2055e5a> <174.lean @ 81b79068> Challenge.lean Transport.lean --planted`; both pins' sha256 checked (`b6ac1bcd…`, `c0e0dcb3…`) | **PASS**: `IsRamsey` with its docstring (539 bytes) identical to both; Transport.lean's `IsRamsey` (273 bytes) identical to both; `graham_false'` (30 tokens) equal to PR #7706's statement (with `IsRamsey` → `Erdos174.IsRamsey`) and to Transport.lean's; the three planted mutants (`1 ≤ k → 2 ≤ k`, `A.Finite →` dropped, the docstring's `k ≥ 1 → k ≥ 2`) FAIL as required | 0 | 0.02 s | — |
| verbatim, v1.0.0's checks | `checks/verbatim_check.py` (Transport.lean against 2055e5a); `checks/verbatim_seven.py … --planted` (Seven.lean against OpenAI's NineStatement.lean and EuclideanRamseyNine.lean, both pins checked) | **PASS** both; the two planted mutants FAIL as required | 0; 0 | 0.03 s | — |
| cache | `lake exe cache get` into an empty `.lake` | done | 0 | 1 min 20.3 s | 1.01 GB |
| **build** | `lake build` (default targets OAI, HeptagonRamsey, Challenge, Solution) | **green**, 8,965 jobs; the only warnings are the four intended `declaration uses 'sorry'` in Challenge.lean; Solution.lean prints `depends on axioms: [propext, Classical.choice, Quot.sound]` for each of the four theorems | 0 | 1 min 20.2 s | 3.02 GB |
| exports | `lake env leanexport Challenge -- …`; `… Solution -- …` (lean4export format 3.1.0, as bundled) | Challenge 85,690,960 bytes, sha256 `47f346c157c7783c4229c220ee752d9f4daac8478df4ca37d4783ea4b822bc41`; Solution 232,345,444 bytes, sha256 `36c6a339d8f669400af2d7f7c03942cada712f9376061660b39acd6473be2968` | 0; 0 | 14.8 s; 23.3 s | 6.62 GB; 6.74 GB |
| **comparison + axioms** | `lake comparator --config comparator.json --challenge-from-export … --solution-from-export …` | **pass** for all four theorems: no statement or constant mismatch, no illegal axiom; then stopped at the kernel spawn (`bwrap`), see above | 1 | 14.6 s | 0.54 GB |
| comparator, sandboxed | `scripts/verify-comparator.sh` (PalomarTemplate, unmodified) | **no verdict**: "Resolving dependencies", then `bwrap: No permissions to create new namespace` | 1 | 10.2 s | 0.85 GB |
| **Lean kernel** | `leanchecker --silent --from-export <Solution export>` | **accept** | 0 | 47.3 s | 0.48 GB |
| **Lean paranoid** | `leanchecker-paranoid --silent --from-export …` | **accept** | 0 | 58.4 s | 0.46 GB |
| **NanoDa** | bundled `nanoda_bin <config>` (Lake's configuration: the three permitted axioms, 4 threads, Nat and String extensions) | **accept** (it prints nothing on success; see the forged export) | 0 | 10.8 s | 0.38 GB |
| **con-ron** | bundled `con-ron --jobs=2 …` | **accept**: "con-ron: accepted 37059 declarations (--verified)" | 0 | 45.5 s | 0.74 GB |
| **con-leche** | bundled `con-leche …` | **accept**: "con-leche: accepted 37059 declarations (--verified)" | 0 | 23.6 s | 0.88 GB |
| **lean4lean** | bundled `lean4lean --import …` | **accept**: "checked 37060 declarations" | 0 | 56.7 s | 0.40 GB |
| forged export (a control) | a copy of the Solution export in which one record changes: the theorem `HeptagonRamsey.Heptagon.E_ne_zero` (`∀ r, 2 < r → E r ≠ 0`) gets the type of `E_mul`, its proof unchanged (line 3,313,735); the six kernels as above | **all six reject**: leanchecker exit 1; paranoid exit 1; NanoDa `assertion failed: self.def_eq(u, v)` (tc.rs:955), exit 101; con-ron "rejected: type mismatch in declaration [at thm HeptagonRamsey.Heptagon.E_ne_zero, fold position 31361]", exit 1; con-leche "invalid: type mismatch in theorem HeptagonRamsey.Heptagon.E_ne_zero", exit 1; lean4lean exit 134 (a panic, "invalid environment extension has been accessed", with `LEAN_ABORT_ON_PANIC=1`: a crash on the forged input, not a printed verdict) | 1; 1; 101; 1; 1; 134 | 37.3 s; 43.3 s; 10.9 s; 34.8 s; 19.8 s; 45.2 s | ≤ 0.75 GB |
| **negative controls** | `tests/controls/run-controls.sh --from-export` (each control built, exported as above, judged by `lake comparator --…-from-export`) | **6 of 6 refused for the stated reason**: `graham_false'` without `A.Finite` and `heptagon_counterexample` with one point moved and A.3 without the distinctness of `t₁, t₂, t₃`: "Challenge and solution theorem statement do not match"; `IsRamsey` with `2 ≤ k`: "Const does not match between challenge and target 'Erdos174.IsRamsey'"; Challenge as solution: "Illegal axiom detected: 'sorryAx'"; a solution from a planted axiom: "Illegal axiom detected: 'HeptagonRamsey.Heptagon.planted_axiom'" | 0 (each control 1) | 4 min 22.9 s | 6.74 GB |
| **axiom audit** | v1.0.0's `checks/audit.lean` (two computations: its own traversal of the private view of the environment, and `Lean.collectAxioms`), run outside the repository with the two `Statement` modules imported and the three `Lean.ofReduce…`/`trustCompiler` names written as plain names (no constant of those names exists in v4.35.0-rc2, so the double-backtick form no longer
elaborates; the check for them is then trivially empty, and the permitted-axioms check stands) | **PASS** on all nine theorems (below): exactly `propext`, `Classical.choice`, `Quot.sound`, the same by both computations; no forbidden constant, no missing reference, no `implemented_by`/`extern` on a constant of ours | 0 | 26.0 s | 7.20 GB |
| **`leanchecker --fresh`** | `lake env leanchecker --fresh --verbose Solution` (Lean's kernel replays every constant of the module's closure, imported and local, into a fresh environment; run after the record, alone, 21:12:59 Z to 21:43:57 Z) | **accept**: "replaying Solution with --fresh" and nothing else (it prints nothing on success) | 0 | 30 min 57 s | 8.48 GB |
| licence | PalomarSubmission `scripts/detect_license.rb` (commit `14aa8d6b`), licensee 10.1.0 | exactly one licence file at the root, detected as `MIT` (= `project.license`); the same on the commit that adds this file | 0 | — | — |
| metadata | PalomarSubmission `scripts/submission_contract.py` `load_formalization_metadata` and `normalized_provenance` (commit `14aa8d6b`) | **no mechanical issue**; result origin `source-based`, repository role `substantive-development`; the same on the commit that adds this file (with the source rules and `checks/verbatim_palomar.py`, and its 36 `.lean` files compared with the record's: equal) | 0 | — | — |
| port replay (on the Mac) | `scripts/port_to_modules.py` on the upstream files, `diff -r` | `OAI/` identical; `HeptagonRamsey/` identical but for the two new `Statement.lean` files (docs/PORT-LOG.md) | 0 | — | — |
| definitions across Mathlib pins (on the Mac) | curl of Mathlib at `065356127b` (this branch), `d13f23b7` (v1.0.0, OpenAI's) and `0df444a3` (formal-conjectures' at `2055e5a`, Lean v4.33.1) | `Mathlib/Topology/MetricSpace/Congruence.lean` byte-identical at all three (sha256 `7da6267f…`); `EuclideanGeometry.Cospherical` has the same definition at all three | — | — | — |

The exports are reproducible: those of this commit made on an incrementally built development tree and on the fresh
clone are byte-identical, and so were those of the previous commit (`484a9c43`, the same files without the two A.3
statements) on the development tree and on a fresh clone.

What the audit printed for each theorem (closure = transitive constants / modules; "ours" = constants of this
library in the closure):

| theorem | compared | closure | ours |
|---|---|---|---|
| `HeptagonRamsey.Heptagon.heptagon_counterexample` | yes | 33,558 / 1,234 | 97 |
| `HeptagonRamsey.Heptagon.graham_false'` | yes | 36,921 / 1,371 | 102 |
| `HeptagonRamsey.Generic.generic_seven_not_isRamsey` | yes | 34,261 / 1,254 | 126 |
| `HeptagonRamsey.Generic.seven_circle_configuration_isRamsey` | yes | 34,695 / 1,264 | 139 |
| `HeptagonRamsey.Heptagon.not_fieldCriterion` | no | 29,443 / 1,081 | 78 |
| `HeptagonRamsey.Heptagon.not_ramsey` | no | 33,526 / 1,231 | 87 |
| `HeptagonRamsey.Heptagon.graham_false` | no | 36,920 / 1,371 | 101 |
| `HeptagonRamsey.Generic.generic_seven_not_ramsey` | no | 34,239 / 1,250 | 114 |
| `HeptagonRamsey.Generic.seven_circle_configuration` | no | 34,676 / 1,261 | 132 |

Outside our modules every closure holds 5 `implemented_by` and 57 `extern` constants (core primitives; the kernel never
runs compiled code), 0 `unsafe`, 0 `partial`.

## Gaps, named

- **No sandboxed `lake comparator` verdict exists yet.** The comparison and the axiom check ran in `lake comparator`
  itself, on exports made outside its sandbox; the kernel stage ran outside it, binary for binary. Palomar's
  verification workflow, or `scripts/verify-comparator.sh` on a Linux machine where `bwrap` can start (GitHub's
  `ubuntu-latest` with the sysctl the PalomarTemplate CI sets), would give the end-to-end exit.
- **Palomar's own verifier was not run.** It fetches the commit from GitHub, and this branch has not been pushed.
  Its preparation checks that could run locally did (source rules, licence, metadata).
- **NanoDa is silent on success.** Its acceptance is its exit 0, and its rejection of the forged export.
- **lean4lean's rejection of the forged export is a crash** (exit 134 on a panic), not a printed verdict.
- **The transport is to a verbatim copy.** `Erdos174.IsRamsey` here is formal-conjectures' text compiled against
  Mathlib `065356127b`, not formal-conjectures' constant on its Mathlib `0df444a3` (Lean v4.33.1). `Congruent` and
  `Cospherical` were compared across the pins (above); the rest of the definitions' dependencies were not.
- **The Challenge imports all of Mathlib**, as radian-ramsey's does, so that its elaboration sees the instances the
  Solution sees (the Solution imports all of Mathlib through OpenAI's `Model.lean`); a narrower import was not tried.
- **The audit is a copy of v1.0.0's script with one edit** (above), run from outside the repository; this branch
  does not ship it, because a non-module `.lean` file may not be in a Palomar submission.
- **OpenAI's tree is trusted as included.** The 16 ported files are byte-identical to openai/math `4eaee875` but for
  their headers (docs/PORT-LOG.md); their proofs are in the closure the kernels replay.
- **Version 1.0.0's second-kernel record** (nanoda 0.4.31 and con-ron `97eead2d` on a lean4export closure, at Lean
  v4.34.1; CHECKS.md) is not repeated here with those pins; the kernels here are the ones bundled with v4.35.0-rc2.

## sha256 of the files checked

```
0d742cdea41994139200e755214fd983e8db957531b95df2d21135e58ee76a73  Challenge.lean
64be7b47202b4e4baed85fa08a08c9641678601010986d716f3e3cba64a8b3c3  Solution.lean
20a0e08b18f1ade9e3db56f066a662a44853e311e7947ebaf5270b82d3539afe  comparator.json
5f2baba52b59c94b5bd49e6bf4c0fd3fbb5f84a06fc9d4c6a19e2e4a87b7ec52  formalization.yaml
76439f36b95b2007c247ad9754cf68a70375996ecbde1218d8ad17b7d631173d  lakefile.toml
56c2281482ada4f3ca6a321c16be6a1d136a2e8100938fb918cbdac09fbbe159  lake-manifest.json
8dc8d6f560141069d9073e370611716ef77ada0da8ffa37e2149f44b2e63ac7a  lean-toolchain
b9cf5e59100ad8e02ceadcab69d2b89b99b7e180c21b439fddae850f2ce81200  LICENSE
c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4  LICENSES/Apache-2.0.txt
6d99406083ca29090b2b8fd5fe596d9d7d634a58d31670a63878eddeee7d5513  NOTICE
6919911f9905fcc9f01cac96e8c98a348a192a5550a10d127b0b3ced2d74bc5a  scripts/check-lean-sources.py
4fefa0e6c779448143b3164f56e96c3b6f719de67da335fa445127ab55f9b1e2  scripts/verify-comparator.sh
d3facb2ae99ee5d99b96fce816c0148ba5ff8f9c94eafdb427295f8334717379  scripts/port_to_modules.py
480f85d10924ba5fbea63a2d67224aa6beafac124f8bb8ed68102d5bc690359e  checks/verbatim_palomar.py
e8ba69cd405ec587a00ca26ce4c90a175f981e14b8dc971adf43d73cb3c988eb  checks/verbatim_check.py
00a8ce4eda5ccc7ccdc2ab485ad6a1fde60d85d87654d383dc64f714f247511a  checks/verbatim_seven.py
b02feb4da06ed2bc38eff43f0d920974b614ac55b33d5cff472db86452200b6a  tests/controls/run-controls.sh
8bf92eeb1eb36ec817357b6260f423b6f8662f3691d6f177290ae000e95fabde  HeptagonRamsey.lean
c8048f31e6f3a4ca5f625cf80ef005019cbabe89c5c7a28cbe6edf1012ec3c05  HeptagonRamsey/Generic/A3.lean
70bde2a46ead88053aad84be5e3b995cbebc731da46cecf9bbbf57c3d2ece5ee  HeptagonRamsey/Generic/Derivation.lean
e07a84a197df4786a2983554f018c68391a4ccdce41898313318c5fa9039c813  HeptagonRamsey/Generic/LemmaA1.lean
f6308cb67c3eef372e1dc54c778f4d6311249c4caef7cd408d3404a82ad2ed33  HeptagonRamsey/Generic/Moments.lean
d50ae71e4eb66c7e2e79aa3a13c95b2f9ccb81a77a004c443c298aafb478ce96  HeptagonRamsey/Generic/Seven.lean
8a57030288941f28d221c8e3aa04e51127ffbc03609c9ec06c6a076311b99ffe  HeptagonRamsey/Generic/Statement.lean
adb2259e6699e1de219325f42e109287969850ef853653ac4ce7988fee066609  HeptagonRamsey/Heptagon/Criterion.lean
7d89ef17eec1c2fa54de3d6aa36453072bfc4d31e4ee4383a1dd54f2210d7e13  HeptagonRamsey/Heptagon/NotRamsey.lean
9f8892d7bac9de6575269c1ab8946e620679c628131f563cbd06e41c99a85e99  HeptagonRamsey/Heptagon/Pairing.lean
a6787ee9e96d6cc880581c0942b7bad3fe9accef7ac40d459db052ea07a7a2dd  HeptagonRamsey/Heptagon/Points.lean
75b57c49c02ae40eb1fd49feb0d9a398385ec1329ce383697059d84bb4b91614  HeptagonRamsey/Heptagon/Statement.lean
737711ced7b6b7511f99e6ae57975a0f9f062aa70048a0057b45f86ac85ce339  HeptagonRamsey/Heptagon/Transport.lean
```

`formalization.yaml` and `NOTICE` are listed as committed with this file; at `ccd8a779` they were `11d4d85c…` and
`1aea1352…`. The 16 files under `OAI/` are listed with their upstream and ported sha256 in docs/PORT-LOG.md, and the
36 `.lean` files of the clone were compared with the committed ones (all equal).
