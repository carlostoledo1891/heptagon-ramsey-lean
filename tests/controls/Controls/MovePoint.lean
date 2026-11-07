module

public import Mathlib

@[expose] public section

/-! NEGATIVE CONTROL (the last point `(4, −√(4(2r − 4)))` moved to `(4, −√(4(2r − 3)))`). Comparator must refuse it. -/

/-!
# Advertised statements: Graham's conjecture is false (Pálvölgyi's heptagon)

Mathlib-only. The trusted surface is one definition and two theorem statements.

* `Erdos174.IsRamsey`, with its docstring, is copied byte for byte from google-deepmind/formal-conjectures
  `FormalConjectures/ErdosProblems/174.lean` at 2055e5adadae0b2e392365938faa82ef6f1464f0 (Apache-2.0),
  unchanged at the head of formal-conjectures PR #7706 (81b7906812371c1674f333d71e18d84c0c57e613);
  `checks/verbatim_palomar.py` compares it with both. `Congruent` is Mathlib's
  (`Mathlib.Topology.MetricSpace.Congruence`): a map `p : A → ℝᵈ` with
  `dist (p a) (p b) = dist a b` for all `a b`. As in formal-conjectures, `IsRamsey` allows
  every dimension `d`, including `d = 0`; the proof handles that case (no two distinct points have
  a distance-preserving copy in `ℝ⁰`).
* `heptagon_counterexample` is Pálvölgyi's Theorem 1 (arXiv:2609.23327): for transcendental
  `r > 2`, the seven points `(0, 0)` and `(j, ±√(j(2r − j)))`, `j ∈ {1, 3, 4}`, written out, lie on
  the circle of centre `(r, 0)` and radius `r` and are not Ramsey. Mathlib's `√` is `Real.sqrt`;
  every radicand is positive for `r > 2`.
* `graham_false'` is the negation of Graham's conjecture as formal-conjectures states it
  (`erdos_174.variants.graham`): not every finite cospherical subset of a Euclidean space is
  Ramsey. Its statement is that of formal-conjectures PR #7706, token for token, with
  `IsRamsey` written `Erdos174.IsRamsey` (it is stated outside that namespace).

Theorem A.3 of the appendix of arXiv:2609.23327 and its seven-point form are proved in this
repository (`HeptagonRamsey/Generic/`) in OpenAI's vocabulary; they are not advertised here.
-/

namespace Erdos174

-- BEGIN VERBATIM (FormalConjectures/ErdosProblems/174.lean @ 2055e5a, `IsRamsey` with its docstring)
/-- A finite set `A ⊆ ℝⁿ` is Ramsey if for every number `k ≥ 1` of colours there is a
dimension `d` such that every colouring of `ℝᵈ` with `k` colours has a monochromatic copy of
`A`. A copy of `A` is the image of a map `p : A → ℝᵈ` that preserves all distances. -/
def IsRamsey {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  A.Finite ∧ ∀ k : ℕ, 1 ≤ k → ∃ d : ℕ, ∀ c : EuclideanSpace ℝ (Fin d) → Fin k,
    ∃ p : A → EuclideanSpace ℝ (Fin d),
      Congruent (fun a : A ↦ (a : EuclideanSpace ℝ (Fin n))) p ∧ ∃ i, ∀ a, c (p a) = i
-- END VERBATIM

end Erdos174

namespace HeptagonRamsey.Heptagon

/-- **Pálvölgyi's Theorem 1** (arXiv:2609.23327): for every transcendental `r > 2`, the seven
points `(0, 0)`, `(1, ±√(2r − 1))`, `(3, ±√(3(2r − 3)))` and `(4, ±√(4(2r − 4)))` lie on the circle
of centre `(r, 0)` and radius `r`, and they are not Ramsey. -/
theorem heptagon_counterexample (r : ℝ) (hr : 2 < r) (ht : Transcendental ℚ r) :
    let S : Set (EuclideanSpace ℝ (Fin 2)) :=
      {!₂[0, 0], !₂[1, √(2 * r - 1)], !₂[1, -√(2 * r - 1)],
        !₂[3, √(3 * (2 * r - 3))], !₂[3, -√(3 * (2 * r - 3))],
        !₂[4, √(4 * (2 * r - 4))], !₂[4, -√(4 * (2 * r - 3))]}
    S ⊆ Metric.sphere !₂[r, 0] r ∧ ¬ Erdos174.IsRamsey S := by
  sorry

/-- **Graham's conjecture, as stated in formal-conjectures (`erdos_174.variants.graham`), is
false**: some finite cospherical subset of some `ℝⁿ` is not Ramsey (the heptagon above, at a
transcendental `r > 2`). -/
theorem graham_false' :
    ¬ (∀ {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n))), A.Finite →
      EuclideanGeometry.Cospherical A → Erdos174.IsRamsey A) := by
  sorry

end HeptagonRamsey.Heptagon
