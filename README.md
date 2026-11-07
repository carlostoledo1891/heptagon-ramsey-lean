# heptagon-ramsey-lean

Lean 4 proofs, on OpenAI's Euclidean Ramsey formalization, that **Pálvölgyi's seven-point cyclic set is not Ramsey**
(so Graham's conjecture as stated in google-deepmind/formal-conjectures, `erdos_174.variants.graham`, is false), and of
**Theorem A.3** of the appendix of arXiv:2609.23327 (generic seven points on a circle are not Ramsey), as printed,
without its measure clause.

Graham's conjecture was refuted in September 2026, by Pálvölgyi with ChatGPT (this seven-point cyclic set) and by
OpenAI (a classification of finite Euclidean Ramsey configurations, in Lean, with twelve- and nine-point
counterexamples). The objects and the mathematics here are not ours: the heptagon and Theorem A.3 are from
D. Pálvölgyi, *A cyclic non-Ramsey heptagon*, arXiv:2609.23327 (2026-09-20), whose proofs the paper attributes to
ChatGPT; the classification that decides them is OpenAI's, *A classification of finite Euclidean Ramsey
configurations* (2026-09-23), with its Lean in [openai/math](https://github.com/openai/math). This repository adds
Lean proofs of the two statements through OpenAI's theorem, kernel-checked. The credit order is below.

## What is proved

Toolchain: Lean v4.34.1, built inside openai/math at `4eaee875` (Mathlib `d13f23b7`), whose tree is used unchanged
(five lines are appended to its `lean/lakefile.lean` to declare this library; `lakefile-append.lean`). `Ramsey`,
`FieldCriterion`, `Space`, `ramsey_fieldCriterion`, `exists_real_derivation`, `NineGeometry.circlePoint` and
`GrahamSpherical.parameter` are OpenAI's; `Erdos174.IsRamsey` and the statement of `erdos_174.variants.graham` are copied
byte for byte from formal-conjectures at `2055e5a` (checked by `checks/verbatim_check.py`).

**The heptagon.** For `r > 2`, `heptagon r : Fin 7 → Space 2` is the seven points `(0, 0)` and `(j, ±√(j(2r − j)))`,
`j ∈ {1, 3, 4}`, on the circle of centre `(r, 0)` and radius `r` (HeptagonRamsey/Heptagon/Points.lean).

```lean
-- HeptagonRamsey/Heptagon/Criterion.lean:150
theorem not_fieldCriterion (r : ℝ) (hr : 2 < r) (ht : Transcendental ℚ r) :
    ¬ FieldCriterion (heptagon r)

-- HeptagonRamsey/Heptagon/NotRamsey.lean:69
theorem not_ramsey (r : ℝ) (hr : 2 < r) (ht : Transcendental ℚ r) : ¬ Ramsey (heptagon r)

-- HeptagonRamsey/Heptagon/Transport.lean:93 and :98
theorem graham_false : ¬ Erdos174.erdos_174.variants.graham.statement
theorem graham_false' :
    ¬ (∀ {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n))), A.Finite →
      EuclideanGeometry.Cospherical A → Erdos174.IsRamsey A)
```

`not_fieldCriterion` is Pálvölgyi's derivation-energy argument run against OpenAI's criterion: a derivation `D` of `ℝ`
with `D r = 1` (their `exists_real_derivation`), the pairing `x ⊗ y ↦ D x · D y` on their tensor ring
`Coeff a ⊗[ℚ] Coeff a`, the weights `2, −2, −2, 2, 2, −1, −1`, and the energy `−24/((2r−1)(2r−3)(2r−4)) ≠ 0`.
`not_ramsey` follows by the necessity half of their classification (`TensorDescent.ramsey_fieldCriterion`), the seven
points spanning the plane by their `circle_five_affineSpan`. `graham_false` refutes formal-conjectures' statement at
`r₀ = 2 + GrahamSpherical.parameter` (transcendental); the `d = 0` case allowed by formal-conjectures' `IsRamsey` is
handled as in formal-conjectures issue #7517. `graham_false'` is the same with the statement spelled out; it is the
statement of formal-conjectures PR #7706 (with formal-conjectures' `IsRamsey`, copied verbatim).

**Theorem A.3.** `circ t i = NineGeometry.circlePoint (t i) = ((1 − tᵢ²)/(1 + tᵢ²), 2tᵢ/(1 + tᵢ²))`, the paper's
`p(t)`; `baseField t = ℚ(t₀, t₁, t₂)` as an `IntermediateField ℚ ℝ` (Lean indices are the paper's minus one).

```lean
-- HeptagonRamsey/Generic/A3.lean:104
theorem generic_seven_not_ramsey (t : Fin 7 → ℝ)
    (h3 : Function.Injective (fun i : Fin 3 => t ⟨i.val, by omega⟩))
    (h4 : AlgebraicIndependent (↥(baseField t)) (fun i : Fin 4 => t ⟨i.val + 3, by omega⟩)) :
    ¬ Ramsey (circ t)

-- HeptagonRamsey/Generic/Seven.lean:78 — OpenAI's nine-point statement (NineStatement.lean) with Fin 9 → Fin 7
theorem seven_circle_configuration (t : Fin 7 → ℝ)
    (ht : AlgebraicIndependent ℚ t) :
    Function.Injective (literal t) ∧
      (∀ i, dist (literal t i) 0 = 1) ∧
      ¬ Ramsey (literal t)
```

`generic_seven_not_ramsey` is A.3 as printed: three distinct parameters, four algebraically independent over the field
they generate. The proof is the appendix's: Lemma A.1 (in its symmetric form) proved generically in `s` and `d`
(LemmaA1.lean), a derivation vanishing on `ℚ(t₀, t₁, t₂)` with prescribed values on `t₃, …, t₆` (Derivation.lean,
generalising OpenAI's `BasisDerivation` from base `ℚ` to an arbitrary base field), and the weighted moments by Lagrange
interpolation (Moments.lean). One remark on the paper: for A.3's configuration the matrix `Σ λᵢ D(pᵢ) pᵢᵀ` is symmetric
but not zero (`moment_M`), so the proof needs Lemma A.1's symmetric condition; the main text's Equation (2), which asks
for that matrix to vanish, is stronger and does not hold there. The appendix's proof uses Lemma A.1, and so does this one.

`seven_circle_configuration` is OpenAI's `nine_circle_configuration` for seven points, in their literal
parametrisation (token-for-token equal to theirs up to `Fin 9 → Fin 7` and the two names, checked by
`checks/verbatim_seven.py`), proved from `generic_seven_not_ramsey`; the change of base field is Mathlib's
`AlgebraicIndependent.adjoin_of_disjoint` with `IntermediateField.algebraicIndependent_adjoin_iff`. OpenAI's paper
remarks that A.3 "already implies" their nine-point non-Ramsey result by taking a subset.

All six theorems depend on exactly `propext`, `Classical.choice` and `Quot.sound`: no `sorry`, no `native_decide`, no
new axiom (`checks/audit.lean`, two independent computations of the axioms). The checks run, with tools, commits, times
and memory, are in [CHECKS.md](CHECKS.md).

## What is not claimed

- **The "almost every" clause of A.3** ("consequently almost every seven-point subset of a fixed circle is not
  Ramsey"). It needs a measure-zero argument that is not formalized here; `generic_seven_not_ramsey` assumes the
  independence, as OpenAI's nine-point theorem does.
- **The six-point case.** That every six concyclic points are Ramsey, so that seven is the least size of a non-Ramsey
  cyclic set, is not proved here. It was closed in Lean by JD Jones (JD-Jones-ASES/six-concyclic-lean, at the level of
  the criterion) and by wstrinz (wstrinz/algebraic-plus-three-ramsey, end to end through OpenAI's sufficiency theorem).
- **Theorems A.7 and A.12** of the appendix, and every other appendix result except A.3.
- **Minimality of seven in Lean**, for the same reason as the six-point case.
- **Anything about other definitions.** The theorems are about OpenAI's `Ramsey` and `FieldCriterion` (and
  formal-conjectures' `IsRamsey`, for the transport). That these capture the informal notions is their authors'
  formalization, taken as given here. Their proofs, like Mathlib's, are in the closure that the kernels replay.
- **New mathematics.** The argument is the paper's; the Lean is ours.

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
4. **JD Jones and wstrinz** — six concyclic points are Ramsey, in Lean; JD Jones's exact certificate that the heptagon
   fails the criterion, with the pairing argument written out on paper; wstrinz's circle phase diagram, and the
   exact certificate of one instance of A.3 (J2-F7 in wstrinz/spherical-ramsey: three rational and four algebraically
   independent circle points). The Lean proof here is of A.3 as stated, for all admissible parameters.
5. **Anas Khan (anxkhn)** — formal-conjectures PR #7706, which re-tags `erdos_174.variants.graham` as solved with the
   statement `¬ (∀ …)` that `graham_false'` proves.
6. **This repository** — Carlos Toledo, with Claude (Anthropic's AI model): Claude wrote the Lean proofs and the check
   scripts under my direction, and the checks in CHECKS.md were run on a rented CPU machine.

## Layout

```
HeptagonRamsey.lean                imports all ten modules below (not itself a lake module: the glob
                                   `HeptagonRamsey.+` selects the submodules; REPRODUCE.sh elaborates it directly)
HeptagonRamsey/Heptagon/           Pairing (the derivation pairing on OpenAI's tensor ring and the weighted trace),
                                   Points (the heptagon), Criterion (not_fieldCriterion), NotRamsey (not_ramsey),
                                   Transport (formal-conjectures' IsRamsey; graham_false, graham_false')
HeptagonRamsey/Generic/            Derivation (derivations with prescribed values over a base field), Moments (A.3's
                                   weighted moments), LemmaA1 (Lemma A.1, symmetric form), A3 (generic_seven_not_ramsey),
                                   Seven (seven_circle_configuration)
lakefile-append.lean               the five lines appended to openai/math's lean/lakefile.lean
REPRODUCE.sh                       one command: toolchain, pinned clone, cache, build, audit, verbatim checks
checks/audit.lean                  the axiom audit of the six theorems (two computations)
checks/audit-planted.sh            the audit's planted controls (sorry, an axiom, native_decide, … must be refused)
checks/planted-variant.sh          a planted variant (a heptagon weight 2 → 1) must fail to build
checks/verbatim_check.py           Transport.lean's copied text against formal-conjectures' 174.lean at 2055e5a
checks/verbatim_seven.py           Seven.lean's statement against OpenAI's NineStatement.lean and Comparator challenge
PINS.txt                           every upstream commit and the sha256 of every pinned upstream file
CHECKS.md                          the record of the checks
```

The docstrings keep a few labels from the pre-registered plan under which the files were written (`H1`, `H2`,
`Amendment D`); `d/verbatim_seven.py` in Seven.lean's header is `checks/verbatim_seven.py` here. They are left as they
were so that the sources are exactly the files that were checked.

## Reproduce

On a fresh x86_64 Linux machine with git, curl and python3 (16 GB of memory and about 25 GB of disk):

```sh
./REPRODUCE.sh                 # build the three roots, the audit and its planted controls, the verbatim checks
./REPRODUCE.sh --kernels       # also leanchecker --fresh on each root, a closure export, nanoda and con-ron
./REPRODUCE.sh --variant       # also the planted variant
```

The default run took 15 minutes on a fresh 8-vCPU machine, 9 of them cloning openai/math's dependencies and
downloading Mathlib's build cache (CHECKS.md, run B). `--kernels` adds 25 to 40 minutes
and 8.5 GB of memory per `leanchecker --fresh` (three of them; `FRESH_PARALLEL=2` runs two at once) and needs a C
compiler for the two Rust tools.

## License

MIT for the files of this repository ([LICENSE](LICENSE)). openai/math is a pinned dependency, fetched at build time
and never copied here; it is under its own license.
