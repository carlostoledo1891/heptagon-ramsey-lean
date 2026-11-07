# heptagon-ramsey-lean

Lean 4 proofs that **Pálvölgyi's seven-point cyclic set is not Ramsey**, so that the conjecture that every finite
spherical set is Ramsey, as google-deepmind/formal-conjectures states it (`erdos_174.variants.graham`), is false;
and of **Theorem A.3** of the appendix of arXiv:2609.23327 (generic seven points on a circle are not Ramsey), as
printed, without its measure clause. The proofs go through OpenAI's Lean classification of finite Euclidean Ramsey
configurations.

The conjecture, posed by Erdős, Graham, Montgomery, Rothschild, Spencer and Straus (*Euclidean Ramsey theorems. I*,
1973) and called Graham's conjecture in formal-conjectures, was refuted in September 2026, by Pálvölgyi with ChatGPT
(this seven-point cyclic set) and by OpenAI (a classification of finite Euclidean Ramsey configurations, in Lean,
with twelve- and nine-point counterexamples). The objects and the mathematics here are not ours: the heptagon and
Theorem A.3 are from D. Pálvölgyi, *A cyclic non-Ramsey heptagon*, arXiv:2609.23327 (2026-09-20), whose proofs the
paper attributes to ChatGPT; the classification that decides them is OpenAI's, *A classification of finite
Euclidean Ramsey configurations* (2026-09-23), with its Lean in [openai/math](https://github.com/openai/math). This
repository adds Lean proofs of the statements through OpenAI's theorem, kernel-checked. The credit order is below.

## Two builds of the same proofs

- **Tag `v1.0.0`** (commit `914298f37e6f4c7096d924f22f7436cac2dff1e1`) is a library built *inside* openai/math at
  `4eaee875` (Lean v4.34.1, Mathlib `d13f23b7`), with five lines appended to its lakefile. It is the commit that
  formal-conjectures PR #7706 links, and it keeps its own record, [CHECKS.md](CHECKS.md) and [PINS.txt](PINS.txt)
  (both unchanged here; the scripts they name, `REPRODUCE.sh` and the audit, are at that tag).
- **This branch** is the same proofs packaged for the [Palomar registry](https://palomar-registry.org): a
  self-contained Lake project at Lean **v4.35.0-rc2** / Mathlib `065356127b` (the PalomarTemplate pin), every
  `.lean` file in Lean's module system. The 16 files of openai/math that the proofs import are included under
  `OAI/`, ported by header-only changes (Apache-2.0; [NOTICE](NOTICE), [docs/PORT-LOG.md](docs/PORT-LOG.md)). Our ten
  modules went through the same header pass; **no statement and no proof was changed**, none needed changing at the
  new toolchain, and two modules, `HeptagonRamsey/Heptagon/Statement.lean` and `HeptagonRamsey/Generic/Statement.lean`,
  were added for the Mathlib-vocabulary statements below. Its record is [CHECKS-PALOMAR.md](CHECKS-PALOMAR.md).

## The advertised statements (`Challenge.lean`)

`Challenge.lean` imports only Mathlib. It holds one definition, formal-conjectures' `Erdos174.IsRamsey` with its
docstring, copied byte for byte from `FormalConjectures/ErdosProblems/174.lean` at `2055e5a` (unchanged at the head
of PR #7706, `81b79068`; `checks/verbatim_palomar.py` compares both), and four theorem statements:

```lean
/-- A finite set `A ⊆ ℝⁿ` is Ramsey if for every number `k ≥ 1` of colours there is a
dimension `d` such that every colouring of `ℝᵈ` with `k` colours has a monochromatic copy of
`A`. A copy of `A` is the image of a map `p : A → ℝᵈ` that preserves all distances. -/
def IsRamsey {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  A.Finite ∧ ∀ k : ℕ, 1 ≤ k → ∃ d : ℕ, ∀ c : EuclideanSpace ℝ (Fin d) → Fin k,
    ∃ p : A → EuclideanSpace ℝ (Fin d),
      Congruent (fun a : A ↦ (a : EuclideanSpace ℝ (Fin n))) p ∧ ∃ i, ∀ a, c (p a) = i

theorem HeptagonRamsey.Heptagon.heptagon_counterexample (r : ℝ) (hr : 2 < r) (ht : Transcendental ℚ r) :
    let S : Set (EuclideanSpace ℝ (Fin 2)) :=
      {!₂[0, 0], !₂[1, √(2 * r - 1)], !₂[1, -√(2 * r - 1)],
        !₂[3, √(3 * (2 * r - 3))], !₂[3, -√(3 * (2 * r - 3))],
        !₂[4, √(4 * (2 * r - 4))], !₂[4, -√(4 * (2 * r - 4))]}
    S ⊆ Metric.sphere !₂[r, 0] r ∧ ¬ Erdos174.IsRamsey S

theorem HeptagonRamsey.Heptagon.graham_false' :
    ¬ (∀ {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n))), A.Finite →
      EuclideanGeometry.Cospherical A → Erdos174.IsRamsey A)

theorem HeptagonRamsey.Generic.generic_seven_not_isRamsey (t : Fin 7 → ℝ)
    (h3 : Function.Injective ![t 0, t 1, t 2])
    (h4 : AlgebraicIndependent ↥(IntermediateField.adjoin ℚ ({t 0, t 1, t 2} : Set ℝ))
      ![t 3, t 4, t 5, t 6]) :
    ¬ Erdos174.IsRamsey (Set.range fun i : Fin 7 =>
      !₂[(1 - t i ^ 2) / (1 + t i ^ 2), 2 * t i / (1 + t i ^ 2)])

theorem HeptagonRamsey.Generic.seven_circle_configuration_isRamsey (t : Fin 7 → ℝ)
    (ht : AlgebraicIndependent ℚ t) :
    let a : Fin 7 → EuclideanSpace ℝ (Fin 2) := fun i =>
      !₂[(1 - t i ^ 2) / (1 + t i ^ 2), 2 * t i / (1 + t i ^ 2)]
    Function.Injective a ∧ (∀ i, a i ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) ∧
      ¬ Erdos174.IsRamsey (Set.range a)
```

- **`heptagon_counterexample`** is Theorem 1 of arXiv:2609.23327 as printed: for every transcendental `r > 2`, the
  seven points `(0, 0)` and `(j, ±√(j(2r − j)))`, `j ∈ {1, 3, 4}`, lie on the circle `(x − r)² + y² = r²` and are
  not Ramsey. The points are written out (`j(2r − j)` evaluated), with Mathlib's `Real.sqrt`; every radicand is
  positive for `r > 2`. "On the circle" is membership in `Metric.sphere (r, 0) r`.
- **`graham_false'`** says that not every finite cospherical subset of a Euclidean space is Ramsey. It is the
  statement of `erdos_174.variants.graham` in formal-conjectures PR #7706, token for token, with `IsRamsey` written
  `Erdos174.IsRamsey` because it is stated outside that namespace (`checks/verbatim_palomar.py`).
- **`generic_seven_not_isRamsey`** is Theorem A.3 of the paper's appendix as printed, without its measure clause:
  for distinct `t₁, t₂, t₃` and `t₄, …, t₇` algebraically independent over `K = ℚ(t₁, t₂, t₃)`, the set
  `{p(t₁), …, p(t₇)}`, `p(t) = ((1 − t²)/(1 + t²), 2t/(1 + t²))`, is not Ramsey. Lean indices are the paper's minus
  one; `K` is Mathlib's `IntermediateField.adjoin ℚ {t₁, t₂, t₃}` inside `ℝ`. The paper labels its appendix
  "by ChatGPT — unchecked"; this is a Lean check of A.3.
- **`seven_circle_configuration_isRamsey`** is A.3's corollary for `t₁, …, t₇` algebraically independent over `ℚ`, in
  the shape of OpenAI's nine-point statement (`nine_circle_configuration`, nine replaced by seven): the seven points
  are distinct, lie on the unit circle, and are not Ramsey.
- **`IsRamsey`** is formal-conjectures' definition: `A` finite, and for every number of colours `k ≥ 1` some
  dimension `d` such that every `k`-colouring of `ℝᵈ` has a monochromatic distance-preserving copy of `A`
  (Mathlib's `Congruent`). It allows `d = 0`; the proof handles that case (two distinct points have no
  distance-preserving copy in `ℝ⁰`). `EuclideanGeometry.Cospherical` is Mathlib's (some centre and radius at which
  every point of the set lies).

`Solution.lean` imports the proofs; `comparator.json` names the four theorems, no definition holes, and the three
standard axioms. Comparator checks that `Erdos174.IsRamsey` and every other constant the statements mention are
identical in the two environments, and that the four proofs use only `propext`, `Classical.choice` and `Quot.sound`.

## How the proof goes

In `HeptagonRamsey/Heptagon/`, in OpenAI's vocabulary (`Ramsey`, `FieldCriterion`, `Space`):

1. `Points.lean`: `heptagon r : Fin 7 → Space 2`, the seven points, and the weights `2, −2, −2, 2, 2, −1, −1`.
2. `Pairing.lean`, `Criterion.lean`: for a derivation `D` of `ℝ` with `D r = 1` (OpenAI's
   `GrahamSpherical.exists_real_derivation`, `r` being transcendental), the pairing `x ⊗ y ↦ D x · D y` on OpenAI's
   tensor ring `Coeff a ⊗[ℚ] Coeff a`; the four weighted moment matrices of the heptagon against `D` vanish except
   the `(y, y)` entry of `Σλ (DA)(DA)ᵀ`, which is the energy `E r = −24/((2r−1)(2r−3)(2r−4)) ≠ 0`; through the
   weighted trace of the criterion's identity this contradicts OpenAI's `FieldCriterion` (`not_fieldCriterion`).
3. `NotRamsey.lean`: the seven points span the plane (OpenAI's `circle_five_affineSpan`), so the necessity half of
   OpenAI's classification (`TensorDescent.ramsey_fieldCriterion`) gives `¬ Ramsey (heptagon r)` (`not_ramsey`); the
   points lie on the circle of centre `(r, 0)` and radius `r` (`heptagon_dist_centre`).
4. `Transport.lean`: formal-conjectures' `IsRamsey` of the range gives OpenAI's `Ramsey` of the family (the `d = 0`
   case excluded as above), so the range is not `IsRamsey` (`not_isRamsey`); at `r₀ = 2 + GrahamSpherical.parameter`
   (OpenAI's Liouville-type parameter, transcendental) this refutes formal-conjectures' statement (`graham_false`,
   and `graham_false'` with the statement spelled out).
5. `Statement.lean` (new on this branch): the range of `heptagon r` is the set of seven points written out
   (`range_heptagon`), which gives `heptagon_counterexample`.

In `HeptagonRamsey/Generic/`, Theorem A.3, as in the appendix: Lemma A.1 in its symmetric form, proved generically
in `s` and `d` (`LemmaA1.lean`); a derivation vanishing on `K = ℚ(t₁, t₂, t₃)` with prescribed values on
`t₄, …, t₇` (`Derivation.lean`, generalising OpenAI's `BasisDerivation` from base `ℚ` to an arbitrary base field);
the weighted moments by Lagrange interpolation (`Moments.lean`); then `not_fieldCriterion` and, through the
necessity half again, `generic_seven_not_ramsey` for `circ t i = NineGeometry.circlePoint (t i)` (`A3.lean`), and
`seven_circle_configuration` with Mathlib's `AlgebraicIndependent.adjoin_of_disjoint` (`Seven.lean`).
`Statement.lean` (new on this branch) transports both to formal-conjectures' `IsRamsey`, for any finite family
(`ramsey_of_isRamsey_range`: a copy in `ℝ⁰` forces the family to be constant, and a constant family is Ramsey).
One remark on the paper, from v1.0.0: for A.3's configuration the matrix `Σ λᵢ D(pᵢ) pᵢᵀ` is symmetric but not zero
(`moment_M`), so the proof needs Lemma A.1's symmetric condition; the main text's Equation (2), which asks for that
matrix to vanish, is stronger and does not hold there.

The OpenAI-vocabulary theorems of v1.0.0 are all still here and still proved, and are not among the compared
declarations: `not_fieldCriterion`, `not_ramsey`, `graham_false`, `generic_seven_not_ramsey`,
`seven_circle_configuration` ([CHECKS.md](CHECKS.md) describes them; `checks/verbatim_seven.py` still compares the
last with OpenAI's text).

All nine theorems depend on exactly `propext`, `Classical.choice` and `Quot.sound`: no `sorry`, no
`native_decide`, no new axiom ([CHECKS-PALOMAR.md](CHECKS-PALOMAR.md)).

## What is not claimed

- **The remark "one may take r = π"** of Theorem 1. The witness for `graham_false'` is `r₀ = 2 + parameter`.
- **The "almost every" clause of A.3** ("consequently almost every seven-point subset of a fixed circle is not
  Ramsey"). It needs a measure-zero argument that is not formalized here; `generic_seven_not_isRamsey` assumes the
  independence, as OpenAI's nine-point theorem does.
- **The six-point case.** That every six concyclic points are Ramsey, so that seven is the least size of a non-Ramsey
  cyclic set, is not proved here. It was closed in Lean by JD Jones (JD-Jones-ASES/six-concyclic-lean, at the level of
  the criterion) and by Will Strinz (wstrinz/algebraic-plus-three-ramsey, end to end through OpenAI's sufficiency
  theorem).
- **Theorems A.7 and A.12** of the appendix, and every other appendix result except A.3.
- **Minimality of seven in Lean**, for the same reason as the six-point case.
- **The classification itself.** It is OpenAI's, used through their Lean proof (16 files included here, ported).
- **Anything about other definitions.** The compared statements use formal-conjectures' `IsRamsey` and Mathlib only;
  the other theorems are about OpenAI's `Ramsey` and `FieldCriterion`. That these capture the informal notions is
  their authors' formalization, taken as given here. Their proofs, like Mathlib's, are in the closure that the
  kernels replay.
- **New mathematics, or a first refutation in Lean.** The argument is the paper's, and OpenAI's Lean already proves
  that an explicit twelve-point set on the unit circle is not Ramsey in their vocabulary; the Lean here is ours.

## Credit, in order

1. **Dömötör Pálvölgyi with ChatGPT** — the heptagon, its weights and derivation certificate, and the appendix with
   Theorem A.3 (arXiv:2609.23327v1). The paper says of its proofs: "I (Dömötör Pálvölgyi) contributed nothing to the
   proofs or ideas, I only gave suggestions about the presentation", and labels the appendix "by ChatGPT — unchecked".
2. **OpenAI** — the classification of finite Euclidean Ramsey configurations and its Lean (openai/math), on which every
   proof here stands: the criterion, its necessity theorem, the real derivations, the circle lemmas, the transcendental
   parameter, and the nine-point statement that `seven_circle_configuration` follows.
3. **pw (byclaude)** — formal-conjectures issue #7517: the pattern for transporting OpenAI's `Ramsey` to
   formal-conjectures' `IsRamsey` (the verbatim copy and the `d = 0` case), and `palvolgyi_check.py`, an exact check of
   the heptagon's identities.
4. **JD Jones and Will Strinz (wstrinz)** — six concyclic points are Ramsey, in Lean; JD Jones's exact certificate
   that the heptagon fails the criterion, with the pairing argument written out on paper; Will Strinz's circle phase
   diagram, the exact certificate of one instance of A.3 (J2-F7 in wstrinz/spherical-ramsey: three rational and four
   algebraically independent circle points), and the module-system port of OpenAI's files in wstrinz/radian-ramsey
   (Palomar PALOMAR-2026-10-18-000020), whose port script and negative-control runner this branch adapts.
5. **Anas Khan (anxkhn)** — formal-conjectures PR #7706, which re-tags `erdos_174.variants.graham` as solved with the
   statement `¬ (∀ …)` that `graham_false'` proves.
6. **This repository** — Carlos Toledo, with Claude (Anthropic's AI model): the Lean was written by Claude under my
   direction, as were the check scripts and this packaging, and the checks were run on a rented CPU machine.

## Layout

```
Challenge.lean                     the advertised statements (Mathlib only); `sorry` by design
Solution.lean                      imports the proofs; `#print axioms` of the four theorems
comparator.json                    the four theorems, no definition holes, the three standard axioms
formalization.yaml                 Palomar's metadata (formalization.yaml v0.4)
HeptagonRamsey.lean                imports every module below
HeptagonRamsey/Heptagon/           Pairing, Points, Criterion (not_fieldCriterion), NotRamsey (not_ramsey),
                                   Transport (IsRamsey; graham_false, graham_false'), Statement (heptagon_counterexample)
HeptagonRamsey/Generic/            Derivation, Moments, LemmaA1, A3 (generic_seven_not_ramsey), Seven,
                                   Statement (generic_seven_not_isRamsey, seven_circle_configuration_isRamsey)
OAI/Combinatorics/                 the 16 openai/math files the proofs import, ported (Apache-2.0)
tests/controls/                    six negative controls for lake comparator and their runner
checks/verbatim_palomar.py         Challenge.lean's IsRamsey and graham_false' against formal-conjectures
checks/verbatim_check.py           Transport.lean's copied text against formal-conjectures at 2055e5a (from v1.0.0)
checks/verbatim_seven.py           Seven.lean's statement against OpenAI's (from v1.0.0)
scripts/check-lean-sources.py      Palomar's module-header and line-count rules (PalomarTemplate, unmodified)
scripts/verify-comparator.sh       lake comparator as Palomar runs it (PalomarTemplate, unmodified)
scripts/port_to_modules.py         the header pass (docs/PORT-LOG.md)
CHECKS-PALOMAR.md                  the record of the checks on this branch
CHECKS.md, PINS.txt                the record and the pins of v1.0.0, unchanged
```

## Reproduce

On x86_64 Linux with git, curl, python3 and `bwrap` (bubblewrap, for `lake comparator`'s sandbox):

```sh
python3 scripts/check-lean-sources.py     # every .lean file a module, at most 10,000 lines
lake exe cache get                        # Mathlib's build cache
lake build                                # everything; prints the axioms of the four theorems
./scripts/verify-comparator.sh            # lake comparator with Lean's kernel, NanoDa and con-ron
bash tests/controls/run-controls.sh       # each of the six controls must be refused
```

Where `bwrap` cannot start (inside an unprivileged container, for instance), `bash tests/controls/run-controls.sh
--from-export` judges exports made with the toolchain's own `leanexport`; CHECKS-PALOMAR.md records how the clean
configuration was judged that way.

## License

MIT for the files written for this repository ([LICENSE](LICENSE)); the 16 ported openai/math files are under the
Apache License 2.0 ([LICENSES/Apache-2.0.txt](LICENSES/Apache-2.0.txt)), and the copied formal-conjectures text and
the PalomarTemplate scripts are Apache-2.0 too. [NOTICE](NOTICE) lists every file's licence.
