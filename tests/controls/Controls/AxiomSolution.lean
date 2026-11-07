module

public import Mathlib

@[expose] public section

/-! NEGATIVE CONTROL (all four theorems proved from a planted axiom `planted_axiom : False`). Comparator must refuse it as a solution. -/

/-!
# Advertised statements: Graham's conjecture is false (Pálvölgyi's heptagon)

Mathlib-only. The trusted surface is one definition and four theorem statements.

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

* `generic_seven_not_isRamsey` is Theorem A.3 of the appendix of arXiv:2609.23327 as printed,
  without its measure clause ("consequently almost every seven-point subset of a fixed circle is
  not Ramsey", which is not formalized): for distinct `t₁, t₂, t₃` and `t₄, …, t₇` algebraically
  independent over `K = ℚ(t₁, t₂, t₃)` (Mathlib's `IntermediateField.adjoin`), the set of the seven
  points `p(tᵢ) = ((1 − tᵢ²)/(1 + tᵢ²), 2tᵢ/(1 + tᵢ²))` is not Ramsey. Lean indices are the
  paper's minus one.
* `seven_circle_configuration_isRamsey` is its corollary for `t₁, …, t₇` algebraically independent
  over `ℚ`, in the shape of OpenAI's nine-point statement (`nine_circle_configuration`, with nine
  replaced by seven): the seven points are distinct, lie on the unit circle, and are not Ramsey.
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

/-- Planted. -/
axiom planted_axiom : False

/-- **Pálvölgyi's Theorem 1** (arXiv:2609.23327): for every transcendental `r > 2`, the seven
points `(0, 0)`, `(1, ±√(2r − 1))`, `(3, ±√(3(2r − 3)))` and `(4, ±√(4(2r − 4)))` lie on the circle
of centre `(r, 0)` and radius `r`, and they are not Ramsey. -/
theorem heptagon_counterexample (r : ℝ) (hr : 2 < r) (ht : Transcendental ℚ r) :
    let S : Set (EuclideanSpace ℝ (Fin 2)) :=
      {!₂[0, 0], !₂[1, √(2 * r - 1)], !₂[1, -√(2 * r - 1)],
        !₂[3, √(3 * (2 * r - 3))], !₂[3, -√(3 * (2 * r - 3))],
        !₂[4, √(4 * (2 * r - 4))], !₂[4, -√(4 * (2 * r - 4))]}
    S ⊆ Metric.sphere !₂[r, 0] r ∧ ¬ Erdos174.IsRamsey S := by
  exact HeptagonRamsey.Heptagon.planted_axiom.elim

/-- **Graham's conjecture, as stated in formal-conjectures (`erdos_174.variants.graham`), is
false**: some finite cospherical subset of some `ℝⁿ` is not Ramsey (the heptagon above, at a
transcendental `r > 2`). -/
theorem graham_false' :
    ¬ (∀ {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n))), A.Finite →
      EuclideanGeometry.Cospherical A → Erdos174.IsRamsey A) := by
  exact HeptagonRamsey.Heptagon.planted_axiom.elim

end HeptagonRamsey.Heptagon

namespace HeptagonRamsey.Generic

/-- **Theorem A.3 of arXiv:2609.23327v1, as printed, without the measure clause**: for distinct
`t₁, t₂, t₃` and `t₄, …, t₇` algebraically independent over `K = ℚ(t₁, t₂, t₃)`, the set of the
seven points `p(tᵢ) = ((1 − tᵢ²)/(1 + tᵢ²), 2tᵢ/(1 + tᵢ²))` is not Ramsey. -/
theorem generic_seven_not_isRamsey (t : Fin 7 → ℝ)
    (h3 : Function.Injective ![t 0, t 1, t 2])
    (h4 : AlgebraicIndependent ↥(IntermediateField.adjoin ℚ ({t 0, t 1, t 2} : Set ℝ))
      ![t 3, t 4, t 5, t 6]) :
    ¬ Erdos174.IsRamsey (Set.range fun i : Fin 7 =>
      !₂[(1 - t i ^ 2) / (1 + t i ^ 2), 2 * t i / (1 + t i ^ 2)]) := by
  exact HeptagonRamsey.Heptagon.planted_axiom.elim

/-- **The seven-point corollary**, in the shape of OpenAI's nine-point statement: for `t₁, …, t₇`
algebraically independent over `ℚ`, the seven points `p(tᵢ)` are distinct, lie on the unit circle,
and their set is not Ramsey. -/
theorem seven_circle_configuration_isRamsey (t : Fin 7 → ℝ) (ht : AlgebraicIndependent ℚ t) :
    let a : Fin 7 → EuclideanSpace ℝ (Fin 2) := fun i =>
      !₂[(1 - t i ^ 2) / (1 + t i ^ 2), 2 * t i / (1 + t i ^ 2)]
    Function.Injective a ∧ (∀ i, a i ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) ∧
      ¬ Erdos174.IsRamsey (Set.range a) := by
  exact HeptagonRamsey.Heptagon.planted_axiom.elim

end HeptagonRamsey.Generic
