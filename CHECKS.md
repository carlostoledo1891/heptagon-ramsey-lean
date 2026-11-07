# CHECKS — the record of the checks on this tree (2026-11-07)

Every check below ran on the files of this commit, by `REPRODUCE.sh` itself, on a RunPod CPU machine (8 vCPU, 64 GB
cgroup memory limit, Ubuntu 24.04.3, Linux 6.8, x86_64, Python 3.12.3). Every process ran under `taskset` on the
container's eight CPUs. The chain: Lean v4.34.1 (`5045d0056413266e57c625dcd7c365b10e377c52`), openai/math at
`4eaee87548250b2682affda7d05d947c05554bae` (sparse checkout of `lean/`), Mathlib `d13f23b7` via `lake exe cache get`.
Wall clock and maxRSS come from `/usr/bin/time -v`; maxRSS is its "Maximum resident set size" in KiB, written here as
GB = KiB ÷ 10⁶. Raw logs are kept outside the repository.

- **Run A** (the record): `WORK=/root FRESH_PARALLEL=2 ./REPRODUCE.sh --kernels --variant`, 2026-11-07 15:29:28 Z to
  16:47:27 Z (1 h 18 min). Its workspace had been prepared by the same commands (elan with v4.34.1, the sparse clone at the pin,
  `lake exe cache get`, and builds of two OpenAI modules). Every olean of ours was deleted before the run, so every
  module of ours was compiled in it. Result: **REPRODUCE: ALL CHECKS PASSED**.
- **Run B** (the one-command path on a fresh box): `env -i HOME=<new> ELAN_HOME=<new> WORK=<new> ./REPRODUCE.sh`,
  15:29:47 Z to 15:44:30 Z (14 min 43 s), on the same machine while run A was running. elan was installed by the
  script (elan 4.2.4), and the clone, the dependencies and the cache were all fetched from nothing. Result: **REPRODUCE:
  ALL CHECKS PASSED**. Its `audit.json` is byte-identical to run A's (sha256 `336fea20…b570`).

## The table

| check | tool + version | verdict | exit | wall | maxRSS |
|---|---|---|---|---|---|
| upstream tree | `git rev-parse`; sha256 against PINS.txt | openai/math at `4eaee875`; 78 of its 79 pinned `lean/` files equal to PINS.txt; `lean/lakefile.lean` = the pinned file (`fc590a5d…`) + `lakefile-append.lean` (`f649e030…`), now `555a98ce…`; `git status`: nothing else changed | — | — | — |
| cache (A) | `lake exe cache get` | done | 0 | 41.5 s | 1.76 GB |
| cache (B, fresh) | the same, from nothing | done | 0 | 8 min 49.6 s | 1.98 GB |
| **(a) build of the three roots** (A) | `lake build HeptagonRamsey.Heptagon.Transport HeptagonRamsey.Generic.A3 HeptagonRamsey.Generic.Seven`, Lean v4.34.1 | **green**, 8,949 jobs, our ten modules compiled, no warning from our files | 0 | 65.8 s | 6.99 GB |
| (a) the same (B) | the same | **green**, 8,949 jobs | 0 | 2 min 11.5 s | 7.00 GB |
| root file (A; B) | `lake env lean HeptagonRamsey.lean` | elaborates | 0; 0 | 27.5 s; 28.2 s | 6.88 GB |
| **(b) axiom audit** (A; B) | `checks/audit.lean`: two computations (its own traversal of the dependency closure, and `Lean.collectAxioms`) | **PASS** on all six theorems: exactly `propext`, `Classical.choice`, `Quot.sound`, the same by both computations; no forbidden constant, no missing reference, no `implemented_by`/`extern` on a constant of ours | 0; 0 | 37.0 s; 43.2 s | 7.26 GB |
| (b) the audit's planted controls (A; B) | `checks/audit-planted.sh` | 8 of 8 as required: `sorry`, a planted axiom, `native_decide` (its auxiliary axiom), `Lean.trustCompiler`, `@[implemented_by]`, `@[extern]` and a `def` as target REFUSED; the clean `2 + 2 = 4 := rfl` PASS | 0; 0 | 25.7 s; 26.6 s | 7.24 GB |
| **(c) `leanchecker --fresh`** Transport | leanchecker of Lean v4.34.1, `--fresh --verbose HeptagonRamsey.Heptagon.Transport` | **accept**: "replaying HeptagonRamsey.Heptagon.Transport with --fresh" and nothing else (leanchecker prints nothing on success) | 0 | 37 min 32 s | 8.54 GB |
| **(c) `leanchecker --fresh`** A3 | the same, `HeptagonRamsey.Generic.A3` | **accept** (the same output for its module) | 0 | 37 min 37 s | 8.54 GB |
| **(c) `leanchecker --fresh`** Seven | the same, `HeptagonRamsey.Generic.Seven` | **accept** (the same output for its module; run alone after the first two) | 0 | 35 min 56 s | 8.54 GB |
| names check | `lake env lean` | 39 of 39 present (the six theorems and 33 kernel-arena prelude names) | 0 | 31.5 s | 6.89 GB |
| **(d) closure export** | lean4export tag v4.34.0 = `076e8e57`, built on v4.34.1 (binary sha256 `8c5d64ba…`), format 3.1.0; modules Transport and Seven, the 39 names | 231,046,358 bytes, 4,305,556 lines, sha256 `90763eca445e724fcd8b1641b7102a1287808424b687e56d34793b85c2cad1f6` | 0 | 39.9 s | 6.79 GB |
| **(d) nanoda** | nanoda_lib 0.4.31 = `8de7e0c4` (binary `60a6c422…`), hard axiom error ON, permitted exactly `propext`, `Quot.sound`, `Classical.choice`; 6 threads, 1 GiB stack | **accept**: "Checked 38527 declarations with no typechecker errors" (and its usual "1 pretty printer errors: [Unable to print axioms]", a display note) | 0 | 10.3 s | 0.35 GB |
| **(d) con-ron** | con-ron `97eead2d` (binary `67bd985e…`), `--verified --jobs=4` | **accept**: "con-ron: accepted 36840 declarations (--verified)" | 0 | 7.9 s | 0.52 GB |
| (d) forged export (a control beyond the plan) | a copy of the export in which ONE record changes: the theorem `HeptagonRamsey.Heptagon.E_ne_zero` (`∀ r, 2 < r → E r ≠ 0`) is given the type of `E_mul`, its proof unchanged (first differing byte 158,178,842); nanoda (2 threads) and con-ron (`--jobs=2`) | **both reject**: nanoda `assertion failed: self.def_eq(u, v)` (tc.rs:985); con-ron "rejected: type mismatch in theorem [at theorem HeptagonRamsey.Heptagon.E_ne_zero, fold position 28041] (--verified)" | 101; 1 | 12.0 s; 9.5 s | 0.27 GB; 0.45 GB |
| **(e) verbatim, formal-conjectures** (A; B; and on a second machine against a read-only copy of the pin) | `checks/verbatim_check.py <174.lean at 2055e5a> Transport.lean`; the pin's sha256 `b6ac1bcd…` checked | **PASS**: 273 bytes of `IsRamsey` and 113 bytes of the `graham` statement identical to the pin | 0 | < 1 s | — |
| (e) its control | the same on Transport.lean with `1 ≤ k` → `2 ≤ k` | **FAIL, as required** | 1 | < 1 s | — |
| **(e) verbatim, OpenAI's nine-point statement** (A; B; second machine) | `checks/verbatim_seven.py Seven.lean NineStatement.lean EuclideanRamseyNine.lean --planted`; both pins' sha256 checked | **PASS** against both files: the def 67 tokens each, the statement 50 each; the raw differences are exactly `literalCircleConfig → literal`, `nine_ → seven_circle_configuration` and the `9 → 7` of the two `Fin 9`; the two planted mutants (`^2 → ^3`, `¬` dropped) FAIL as required | 0 | < 1 s | — |
| **(f) planted variant W** | `checks/planted-variant.sh`: the heptagon's first weight `2 → 1` (`lam` and `lam_0` in Points.lean) | **refused by the build**: `lake build` of the three roots exit 1, `HeptagonRamsey/Heptagon/Criterion.lean:48:18: unsolved goals` (the `none, none` case of `moment0`, `Σλ = 0`, reduces to `False`) | 1 | (73.5 s for the whole script) | 6.99 GB |
| (f) restore | the same | originals restored, their sha256 equal to the originals'; `lake build` green (8,950 jobs) | 0 | (same) | (same) |
| definitions across Mathlib pins (second machine) | curl of Mathlib at `d13f23b7` (OpenAI's) and `0df444a3` (formal-conjectures' at `2055e5a`) | `Mathlib/Topology/MetricSpace/Congruence.lean` byte-identical at both (sha256 `7da6267f…`); `EuclideanGeometry.Cospherical` has the same definition at both | — | — | — |

Tools built in run A: rustc 1.99.1 (58cf8f9c3 2026-10-13) and cargo 1.99.1 (`rustup`, minimal profile); lean4export
(12 s); nanoda `cargo build --release --locked` (25 s); con-ron `cargo build --release -p con-ron` (49 s).

What the audit printed for each theorem (closure = transitive constants / modules; "ours" = constants of this library in
the closure):

| theorem | closure | ours |
|---|---|---|
| `HeptagonRamsey.Heptagon.not_fieldCriterion` | 29,244 / 1,075 | 78 |
| `HeptagonRamsey.Heptagon.not_ramsey` | 33,335 / 1,225 | 87 |
| `HeptagonRamsey.Heptagon.graham_false` | 36,731 / 1,365 | 101 |
| `HeptagonRamsey.Heptagon.graham_false'` | 36,732 / 1,365 | 102 |
| `HeptagonRamsey.Generic.generic_seven_not_ramsey` | 34,080 / 1,244 | 114 |
| `HeptagonRamsey.Generic.seven_circle_configuration` | 34,515 / 1,255 | 130 |

Outside our modules every closure holds 5 `implemented_by` and 55 `extern` constants (core's `Nat`/`Array`
primitives; the kernel never runs compiled code), 0 `unsafe`, 0 `partial`. As Lean prints them:

```
not_fieldCriterion : ∀ (r : ℝ), 2 < r → Transcendental ℚ r → ¬OAI.EuclideanRamsey.FieldCriterion (HeptagonRamsey.Heptagon.heptagon r)
not_ramsey : ∀ (r : ℝ), 2 < r → Transcendental ℚ r → ¬OAI.EuclideanRamsey.Ramsey (HeptagonRamsey.Heptagon.heptagon r)
graham_false : ¬Erdos174.erdos_174.variants.graham.statement
graham_false' : ¬∀ {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n))), A.Finite → EuclideanGeometry.Cospherical A → Erdos174.IsRamsey A
generic_seven_not_ramsey : ∀ (t : Fin 7 → ℝ), (Function.Injective fun i => t ⟨↑i, ⋯⟩) →
    (AlgebraicIndependent ↥(HeptagonRamsey.Generic.baseField t) fun i => t ⟨↑i + 3, ⋯⟩) →
      ¬OAI.EuclideanRamsey.Ramsey (HeptagonRamsey.Generic.circ t)
seven_circle_configuration : ∀ (t : Fin 7 → ℝ), AlgebraicIndependent ℚ t →
    Function.Injective (HeptagonRamsey.Generic.literal t) ∧
      (∀ (i : Fin 7), dist (HeptagonRamsey.Generic.literal t i) 0 = 1) ∧
        ¬OAI.EuclideanRamsey.Ramsey (HeptagonRamsey.Generic.literal t)
```

## Gaps, named

- **The second kernels read lean4export's output.** nanoda and con-ron check the NDJSON that lean4export wrote; the
  exporter (tag v4.34.0 built on v4.34.1) is trusted to have written the closure faithfully.
- **Only the closure was exported**: the dependency closure of the six theorems plus the 33 prelude names. No
  whole-environment export or whole-environment kernel run was made on this tree.
- **Two second kernels, not four.** lean4lean and con-leche were not run on this tree.
- **`leanchecker --paranoid` does not exist in Lean v4.34.1** (its leanchecker reads only `-v`/`--verbose` and
  `--fresh`), so it was not run.
- **Binaries are pinned by commit, not by bytes.** Two builds of con-ron at the same commit on the same machine gave
  different binaries (`8abeabcc…` in the void attempt below, `67bd985e…` in run A); con-ron is built without `--locked`.
  nanoda (`--locked`) and lean4export gave the same bytes both times.
- **OpenAI's tree is a trusted, pinned dependency.** After `lake exe cache get`, eleven of its packages (belyi,
  formal-schemes, elliptic-curves, tempered-fundamental-groups, oka, orbicurve-cores, pi1, heights, genl,
  tate-curves-theta, iut) report "local changes", in run A and in the fresh run B alike. Their tree ships
  `patches/*-lean4341.patch` for its dependencies; none of the eleven packages is in the closure of any of the six
  theorems (the audit's prefixes: Init, Batteries, Aesop, Mathlib, OAI, HeptagonRamsey).
- **The transport is to a verbatim copy.** `Erdos174.IsRamsey` here is formal-conjectures' text, compiled against
  OpenAI's Mathlib `d13f23b7`, not formal-conjectures' own constant on its Mathlib `0df444a3` (Lean v4.33.1).
  `Congruent` and `Cospherical` were compared across the two Mathlib pins (above); the rest of the definitions'
  dependencies were not.
- **The root file is not a lake module.** The library's glob `HeptagonRamsey.+` (lakefile-append.lean) selects the ten
  submodules, so `HeptagonRamsey.lean` is elaborated with `lake env lean` rather than built; nothing imports it.
- **Run B shared the machine with run A**, so its times are contended. The two parallel `--fresh` runs took 37.5 min
  each on this machine (single-threaded, on a host whose load average was 80–110 at the time).
- **A void attempt, recorded.** The first attempt of run A (15:19 Z, stopped at 15:28 Z) exported from the module
  `HeptagonRamsey`, which is not a lake module (above): the names check and the export failed (exit 1), and nanoda and
  con-ron then ran on the resulting EMPTY file and exited 0 ("Checked 0 declarations", "accepted 0 declarations").
  That is not evidence of anything. REPRODUCE.sh now exports from the two leaf modules, exports only when every name is
  present, runs the kernels only on a non-empty export, and requires a positive declaration count. Run A above is the
  rerun from a clean state; its earlier steps (build, audit, verbatim) had passed in the void attempt as well.

## sha256 of the files checked

```
562f30b9bac2de93429ba15971fd64487b749ac547988956436a2f7528343ae0  HeptagonRamsey.lean
9ecb501e95fd5013efd4d7b2b2731abf50ee3a1ebd4f8a99423fa77e3a52278e  HeptagonRamsey/Generic/A3.lean
7d5bdcbef2b7cd325d4df7d1c6bda3a34d89bec2abe9af680c09d15232f66fde  HeptagonRamsey/Generic/Derivation.lean
5209c3fbf68d8d7802216c51ccf901a1740c7a71281c8dff7d783a4937b51113  HeptagonRamsey/Generic/LemmaA1.lean
8ed3b73f07d656ae243bd99fcf93ae2819b94607aed0bc339f9cab178265eb2f  HeptagonRamsey/Generic/Moments.lean
eed79f156121742078c1326acdd769e5ff48e6b745424871ec453ff7c59cc28f  HeptagonRamsey/Generic/Seven.lean
c4a25c6d24e408b5b8a8a2918a83f367a5e65ec920f76f30f00f28df29c17a56  HeptagonRamsey/Heptagon/Criterion.lean
6d466d3797f60488e7e2b70f9ec73491b617c0bf4f0d464b8c050ffb3c03b3ae  HeptagonRamsey/Heptagon/NotRamsey.lean
3bb5632ebbf394b86c068f3f3faa98cc79b7ab252cbc65c62cf8640495a81f54  HeptagonRamsey/Heptagon/Pairing.lean
8c7a6f3e00affbc306d3d68893e8d9754eb82ea06960bba351e49331b479672a  HeptagonRamsey/Heptagon/Points.lean
76905716ae8769504084f4adb8e9e581924ae721eb756aa2d10b2825e7882b3c  HeptagonRamsey/Heptagon/Transport.lean
76f71787396e1870389ede52bfbd57b5fd33719eb4bb74b791e84dffb760d321  checks/audit.lean
f649e0306f5a01a8abde2bcdac83cc4dd3274c7ce816d552917e298c931fd369  lakefile-append.lean
60018a18a74c152d66b86bb82f4259713c574507f1df1e999ed210e2a2ce0c5c  REPRODUCE.sh
ca8031dd93ce1e3316da1157ad463cd5ed1fb98a590ed8db38b55d3bf3d216ae  checks/audit-planted.sh
ffc6071313a218c7d371d4a4e4b7c319cde1a2187446f4339a301b20af35f17a  checks/planted-variant.sh
e8ba69cd405ec587a00ca26ce4c90a175f981e14b8dc971adf43d73cb3c988eb  checks/verbatim_check.py
00a8ce4eda5ccc7ccdc2ab485ad6a1fde60d85d87654d383dc64f714f247511a  checks/verbatim_seven.py
```

1,443 lines of Lean in the eleven library files; the installed copies on the machine were compared with these
(`sources.sha256`, equal in runs A and B).
