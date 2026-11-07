# Port log: OpenAI's files and this repository's proofs, Lean v4.35.0-rc2

**Pins.**
- From: Lean v4.34.1 / Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, inside openai/math
  `4eaee87548250b2682affda7d05d947c05554bae` (tag `v1.0.0` of this repository, commit
  `914298f37e6f4c7096d924f22f7436cac2dff1e1`, the build linked from formal-conjectures PR #7706).
- To: Lean **v4.35.0-rc2** / Mathlib **`065356127b1dc0016f66b7283ce0ce2c4055aa55`** (Mathlib tag
  `v4.35.0-rc2`, the PalomarTemplate pin). All nine Lake packages are pinned to full SHAs in
  `lake-manifest.json`, which is wstrinz/radian-ramsey's manifest (the same Mathlib pin) with the
  package name changed.

Why: Palomar requires every `.lean` file of a submitted repository to use the Lean module system
and a toolchain of at least v4.35.0-rc2, and judges with the toolchain's own `lake comparator`. At
`v1.0.0` this repository was a library appended to openai/math's Lake package, with no files of
openai/math copied; a Palomar submission must instead be a self-contained module-system project,
so the 16 OpenAI files the proofs import are included here, ported.

## 1. OpenAI's files: header-only changes

`python3 scripts/port_to_modules.py --notice-oai OAI/Combinatorics/*/*.lean`, run once on the
byte-exact upstream files, made in each of the 16 files:

| Change | Lines per file | Why |
|---|---|---|
| Apache-2.0 modification notice, a plain comment before `module` | +8 | Apache-2.0 §4(b); Palomar allows ordinary comments before the header |
| `module` before the imports | +1 | every file must use the module system |
| `import X` → `public import X` | ±0 per import | dependants see the imported declarations |
| `@[expose] public section` after the imports | +1 | every declaration stays public and every definition keeps its body visible downstream: the pre-module behaviour |
| blank lines around those | +2 | layout |

**No other line changed.** The 16 files are the import closure, inside openai/math, of the ten
modules of `HeptagonRamsey/` (computed from the `import` lines; nothing else of openai/math is
imported). Every upstream file was checked against `PINS.txt` (16 of 16 equal). The nine
EuclideanRamsey files are byte-identical at openai/math `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`
(the commit wstrinz/radian-ramsey ported, Palomar entry PALOMAR-2026-10-18-000020) and at
`4eaee875`; their ported files here equal radian-ramsey's (its commit `f94bedbc`) line for line
except line 3, the commit named in the notice. The seven SphericalRamsey files are not in
radian-ramsey; they went through the same pass.

Replay: copy the 16 upstream files at `4eaee875` (`lean/OAI/Combinatorics/<dir>/<file>.lean`) into
a scratch tree `OAI/Combinatorics/<dir>/`, run the command above there, and compare the scratch
tree with `OAI/` by `diff -r` (no difference, 2026-11-07).

| file (here = upstream path under `lean/`) | upstream sha256 at 4eaee875 | ported sha256 | lines | = radian-ramsey port |
|---|---|---|---|---|
| `OAI/Combinatorics/EuclideanRamsey/CircleExtension.lean` | `2f2a541e0c05062185e6c3f8c4d31ae612827248dbd64163e53965ba54d12721` | `148c91ddbf5ff11e4df38947fa6162ba5746eb16fd0848cb450c4033ca5151ec` | 100 → 112 | yes, but for line 3 (the commit in the notice) |
| `OAI/Combinatorics/EuclideanRamsey/CircleGeometry.lean` | `dd8311641a5e67f3a397c8d3090b28b04317e11a4c116f84063dadc8dfd04db6` | `c9092ef7119a124d5d3902ebdd8a76a97318f395d527416709b2494c821ba3fb` | 109 → 121 | yes, but for line 3 (the commit in the notice) |
| `OAI/Combinatorics/EuclideanRamsey/CircleInterpolation.lean` | `ee9da87639daa75c74e57ac91b7dfeb1bbab847666f7ba28323b83cffd9dcad7` | `7bf5ba1e4c876c4c8a65b0fb4088d32e08fc07655731c8d3057c754c060e2af0` | 100 → 112 | yes, but for line 3 (the commit in the notice) |
| `OAI/Combinatorics/EuclideanRamsey/CircleSpan.lean` | `9d474edd1063cbd7e80c51872730518cde7879de1a70da8850f35ff751718f58` | `649f90c3e2b646615303684049c8c73b1b3d8ac9c677b019297f28fc4dea9e94` | 49 → 61 | yes, but for line 3 (the commit in the notice) |
| `OAI/Combinatorics/EuclideanRamsey/Congruence.lean` | `3b2eb58d30db147fb8de0df322142bdc5b8a0b851f151845b813b90f5866a709` | `fa40fff554bcb9a13652c3953d32dab6a0b0fde7582b1dde4f24f37d62a2485b` | 103 → 115 | yes, but for line 3 (the commit in the notice) |
| `OAI/Combinatorics/EuclideanRamsey/Model.lean` | `40b5ceffa11dd08a7d85e8a83e0069d9d0fafeb7d1945030f973cc6717b6a7c1` | `24da28851351672d2369da9013b8fd6b95e5e943d2f84c3df23508705d2af6c8` | 46 → 58 | yes, but for line 3 (the commit in the notice) |
| `OAI/Combinatorics/EuclideanRamsey/NineGeometry.lean` | `463799bdbb850c99ba99a1b9dd13be4e6cea5c3f1724737eaeb9d65dffcf0437` | `afb1ab9b726075614d82e414f313bc9b66c57070559bd91fca2fc6c87ab0bc7a` | 99 → 111 | yes, but for line 3 (the commit in the notice) |
| `OAI/Combinatorics/EuclideanRamsey/TensorDescent.lean` | `0cab41d6f80e3a252c4cb673eaec7afb33cf3d50102d7a0709f74e8b2bbfef48` | `cce2dc0b41e084db16a3144def4c74aa18f418356b8ab4afbecd5eb75a91bdc4` | 162 → 174 | yes, but for line 3 (the commit in the notice) |
| `OAI/Combinatorics/EuclideanRamsey/TensorNecessity.lean` | `417efd25ed39e57b5e04daaef0e131df758bbce803884f7f150ad2354eb3805c` | `be08555d719ffd865bcf1d8df7b505f4a845e728ab6183aeefc740a7290d9e3c` | 262 → 274 | yes, but for line 3 (the commit in the notice) |
| `OAI/Combinatorics/SphericalRamsey/AlgebraicExtension.lean` | `7081c4259a4ff166fde484fec15a55b17e2550231f0b5f81c764be19aa0ce99e` | `e74f4d193e45fc6b0b9fd529cf4c0fcf9ff050b68e4bacadbc85b45dec1ca31f` | 90 → 102 | — (not in radian-ramsey) |
| `OAI/Combinatorics/SphericalRamsey/BasisDerivation.lean` | `4fcbdec83d622cdfc22c50e12cd857634925ce8dcebbc7278051c29cbbf66bda` | `e5d4ab7ace2f621e2da1b4966476f70c534026d13c0b1e9c6c5bc200f5bd0c3d` | 118 → 130 | — (not in radian-ramsey) |
| `OAI/Combinatorics/SphericalRamsey/Model.lean` | `ea48c1c522c7e892c00ac1c64ff671e3e9270565d4ac92edc0bb1df38b2c4ece` | `6f0b40d9e4b87401e01c075e49dd7bbfc048a5a17226ac2f9f09276fd228a0c8` | 66 → 78 | — (not in radian-ramsey) |
| `OAI/Combinatorics/SphericalRamsey/Parameter.lean` | `f430d2fa7863d60570af8a09c602ab7946e950efd81a19d66ffd5519f252ef78` | `ff6a185adf2c384f00b424b2d9a1cfdafa71098f0ffa64d5f000af0936f24ad4` | 48 → 60 | — (not in radian-ramsey) |
| `OAI/Combinatorics/SphericalRamsey/RealDerivation.lean` | `48b28a40e99507ba3b42b660dd533851ce6dd5d5dca920149ec1a08ed64464b7` | `98c0366d5987a5eb7b9b8e6c7cdc27f1abe2b18b2d60828d4440816c9733f27a` | 36 → 48 | — (not in radian-ramsey) |
| `OAI/Combinatorics/SphericalRamsey/RealTranscendenceBasis.lean` | `9a34683d9cb1f4e1603ced381092c1e1e8778c9e9cead316ba181ea19d0955d4` | `97f424af368e970d302d960d24709547d495d791c6a3da36557b419ddf23eb18` | 25 → 37 | — (not in radian-ramsey) |
| `OAI/Combinatorics/SphericalRamsey/Specification.lean` | `e23deee3c8d09c78aecdbb0d39657edd0ea571c898ca68df9eb79a4eab281b29` | `77693c13dbd12e62fad4f77c6fca1285ec03376f524b81f13238add9fd18b551` | 1 → 13 | — (not in radian-ramsey) |

## 2. This repository's files (`HeptagonRamsey/`)

1. **Header pass.** `python3 scripts/port_to_modules.py HeptagonRamsey/*/*.lean HeptagonRamsey.lean`:
   `module`, `public import`, `@[expose] public section`. No notice (these are this
   repository's files). Replay: the same command on the files of tag `v1.0.0`, compared by
   `diff -r` with `HeptagonRamsey/`: no difference except the two new `Statement.lean` files (2026-11-07).
2. **Proof changes needed at the new pin: none.** All ten modules of `v1.0.0` built at Lean
   v4.35.0-rc2 / Mathlib `06535612` on the first attempt, with no edit to any statement, proof,
   `open`, `variable` or option, and with no warning from their files (CHECKS-PALOMAR.md). The
   Mathlib drift between `d13f23b7` (a v4.34.1 branch commit) and `06535612` (69 commits ahead of
   their merge base, 1 behind) touches no name these files use.
3. **The root file.** `HeptagonRamsey.lean` gains `import HeptagonRamsey.Heptagon.Statement` and
   `import HeptagonRamsey.Generic.Statement` before the header pass, and is now a Lake module (at
   `v1.0.0` it was elaborated with `lake env lean` but not built).
4. **Two new modules**, written for the Palomar packaging, so that the advertised statements use
   no definition of this repository's or of OpenAI's (only Mathlib and formal-conjectures'
   `IsRamsey`):
   - `HeptagonRamsey/Heptagon/Statement.lean` (59 lines): `heptagon_counterexample`, Pálvölgyi's
     Theorem 1 with the seven points written out in `EuclideanSpace ℝ (Fin 2)`, proved from
     `range_heptagon` and the existing `not_isRamsey` and `heptagon_dist_centre`;
   - `HeptagonRamsey/Generic/Statement.lean` (83 lines): `ramsey_of_isRamsey_range` (for any
     finite family, formal-conjectures' `IsRamsey` of the range gives OpenAI's `Ramsey`; the
     dimension-0 case forces a constant family), and `generic_seven_not_isRamsey` and
     `seven_circle_configuration_isRamsey`, Theorem A.3 and its corollary with the points
     `p(tᵢ)` written out, proved from the existing `generic_seven_not_ramsey`,
     `seven_circle_configuration` and `literal_eq`.
   Both built on the first attempt.

| file | v1.0.0 sha256 (CHECKS.md) | ported sha256 | lines |
|---|---|---|---|
| `HeptagonRamsey/Generic/A3.lean` | `9ecb501e95fd5013efd4d7b2b2731abf50ee3a1ebd4f8a99423fa77e3a52278e` | `c8048f31e6f3a4ca5f625cf80ef005019cbabe89c5c7a28cbe6edf1012ec3c05` | 113 → 117 |
| `HeptagonRamsey/Generic/Derivation.lean` | `7d5bdcbef2b7cd325d4df7d1c6bda3a34d89bec2abe9af680c09d15232f66fde` | `70bde2a46ead88053aad84be5e3b995cbebc731da46cecf9bbbf57c3d2ece5ee` | 219 → 223 |
| `HeptagonRamsey/Generic/LemmaA1.lean` | `5209c3fbf68d8d7802216c51ccf901a1740c7a71281c8dff7d783a4937b51113` | `e07a84a197df4786a2983554f018c68391a4ccdce41898313318c5fa9039c813` | 132 → 136 |
| `HeptagonRamsey/Generic/Moments.lean` | `8ed3b73f07d656ae243bd99fcf93ae2819b94607aed0bc339f9cab178265eb2f` | `f6308cb67c3eef372e1dc54c778f4d6311249c4caef7cd408d3404a82ad2ed33` | 278 → 282 |
| `HeptagonRamsey/Generic/Seven.lean` | `eed79f156121742078c1326acdd769e5ff48e6b745424871ec453ff7c59cc28f` | `d50ae71e4eb66c7e2e79aa3a13c95b2f9ccb81a77a004c443c298aafb478ce96` | 91 → 95 |
| `HeptagonRamsey/Generic/Statement.lean` | — (new) | `8a57030288941f28d221c8e3aa04e51127ffbc03609c9ec06c6a076311b99ffe` | 83 |
| `HeptagonRamsey/Heptagon/Criterion.lean` | `c4a25c6d24e408b5b8a8a2918a83f367a5e65ec920f76f30f00f28df29c17a56` | `adb2259e6699e1de219325f42e109287969850ef853653ac4ce7988fee066609` | 174 → 178 |
| `HeptagonRamsey/Heptagon/NotRamsey.lean` | `6d466d3797f60488e7e2b70f9ec73491b617c0bf4f0d464b8c050ffb3c03b3ae` | `7d89ef17eec1c2fa54de3d6aa36453072bfc4d31e4ee4383a1dd54f2210d7e13` | 75 → 79 |
| `HeptagonRamsey/Heptagon/Pairing.lean` | `3bb5632ebbf394b86c068f3f3faa98cc79b7ab252cbc65c62cf8640495a81f54` | `9f8892d7bac9de6575269c1ab8946e620679c628131f563cbd06e41c99a85e99` | 139 → 143 |
| `HeptagonRamsey/Heptagon/Points.lean` | `8c7a6f3e00affbc306d3d68893e8d9754eb82ea06960bba351e49331b479672a` | `a6787ee9e96d6cc880581c0942b7bad3fe9accef7ac40d459db052ea07a7a2dd` | 110 → 114 |
| `HeptagonRamsey/Heptagon/Statement.lean` | — (new) | `75b57c49c02ae40eb1fd49feb0d9a398385ec1329ce383697059d84bb4b91614` | 59 |
| `HeptagonRamsey/Heptagon/Transport.lean` | `76905716ae8769504084f4adb8e9e581924ae721eb756aa2d10b2825e7882b3c` | `737711ced7b6b7511f99e6ae57975a0f9f062aa70048a0057b45f86ac85ce339` | 105 → 109 |
| `HeptagonRamsey.lean` | `562f30b9bac2de93429ba15971fd64487b749ac547988956436a2f7528343ae0` | `8bf92eeb1eb36ec817357b6260f423b6f8662f3691d6f177290ae000e95fabde` | 7 → 13 |

The docstrings keep a few labels from the pre-registered plan under which the files were written
(`H1`, `H2`, `Amendment D`); `d/verbatim_seven.py` in Seven.lean's header is
`checks/verbatim_seven.py` here.

## 3. New files

| File | What |
|---|---|
| `Challenge.lean` | Mathlib-only statement surface: formal-conjectures' `Erdos174.IsRamsey` with its docstring, verbatim; `heptagon_counterexample`; `graham_false'` (the statement of formal-conjectures PR #7706, with `IsRamsey` qualified); `generic_seven_not_isRamsey`; `seven_circle_configuration_isRamsey`; each with `sorry` |
| `Solution.lean` | `public import` of the two `Statement` modules, and `#print axioms` for the four theorems |
| `comparator.json` | the four theorems, no definition holes, the three standard axioms |
| `formalization.yaml` | Palomar's metadata (formalization.yaml v0.4) |
| `tests/controls/` | six negative controls (four Challenge edits, a `sorry` solution, a solution from a planted axiom) and their runner, adapted from radian-ramsey's |
| `checks/verbatim_palomar.py` | Challenge.lean's `IsRamsey` against formal-conjectures at `2055e5a` and at the head of PR #7706, and `graham_false'` against PR #7706's statement, with planted mutants |
| `scripts/port_to_modules.py` | the header pass above (radian-ramsey's, with this repository's notice) |
| `scripts/check-lean-sources.py`, `scripts/verify-comparator.sh` | PalomarTemplate `2891de4c`, unmodified |
| `LICENSES/Apache-2.0.txt`, `NOTICE` | the Apache-2.0 text (openai/math's `LICENSE`, byte-identical to PalomarTemplate's and radian-ramsey's) and the licensing of every file |

Removed from this branch (they belong to the openai/math build and stay at tag `v1.0.0`):
`lakefile-append.lean`, `REPRODUCE.sh`, `checks/audit.lean` (a non-module `.lean` file),
`checks/audit-planted.sh`, `checks/planted-variant.sh`.
