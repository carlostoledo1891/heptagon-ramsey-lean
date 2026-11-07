import HeptagonRamsey.Heptagon.NotRamsey
import OAI.Combinatorics.SphericalRamsey.Parameter

/-!
# Transport to formal-conjectures' statement

`Erdos174.IsRamsey` and the statement of `erdos_174.variants.graham` are copied byte for byte from
google-deepmind/formal-conjectures `FormalConjectures/ErdosProblems/174.lean` at 2055e5adadae0b2e392365938faa82ef6f1464f0
(attributes, docstrings and the `:= by sorry` dropped; the theorem's binders and conclusion become a `Prop`);
`verbatim_check.py` compares the copied regions with the pinned file.  `Congruent` is Mathlib's
(`Mathlib.Topology.MetricSpace.Congruence`), as in that file.

`graham_false` refutes the statement with the heptagon at `r₀ = 2 + parameter` (OpenAI's Liouville-type
parameter, transcendental over `ℚ`).  The `d = 0` case of `IsRamsey` (allowed there, not in OpenAI's `Ramsey`)
is handled as in formal-conjectures issue #7517: two distinct points have no distance-preserving copy in `ℝ⁰`.
-/

namespace Erdos174

-- BEGIN VERBATIM (FormalConjectures/ErdosProblems/174.lean @ 2055e5a, `def IsRamsey`)
def IsRamsey {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  A.Finite ∧ ∀ k : ℕ, 1 ≤ k → ∃ d : ℕ, ∀ c : EuclideanSpace ℝ (Fin d) → Fin k,
    ∃ p : A → EuclideanSpace ℝ (Fin d),
      Congruent (fun a : A ↦ (a : EuclideanSpace ℝ (Fin n))) p ∧ ∃ i, ∀ a, c (p a) = i
-- END VERBATIM

set_option linter.unusedVariables false in
/-- The statement of `erdos_174.variants.graham` as a proposition; the binders and the conclusion are the
pinned file's bytes, with the theorem's `:` before the conclusion written `,`. -/
def erdos_174.variants.graham.statement : Prop :=
  ∀
-- BEGIN VERBATIM (FormalConjectures/ErdosProblems/174.lean @ 2055e5a, `theorem erdos_174.variants.graham`, binders)
  {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (hA : A.Finite) (hs : EuclideanGeometry.Cospherical A)
-- END VERBATIM
  , IsRamsey A

end Erdos174

namespace HeptagonRamsey.Heptagon

open OAI OAI.EuclideanRamsey

noncomputable section

/-- In `ℝ⁰` every two points coincide. -/
theorem dist_eq_zero_of_fin_zero (x y : EuclideanSpace ℝ (Fin 0)) : dist x y = 0 := by
  rw [EuclideanSpace.dist_eq]; simp

/-- formal-conjectures' `IsRamsey` for the range of the heptagon gives OpenAI's `Ramsey` for the family. -/
theorem ramsey_of_isRamsey (r : ℝ)
    (h : Erdos174.IsRamsey (Set.range (heptagon r))) : Ramsey (heptagon r) := by
  intro k hk
  obtain ⟨d, hd⟩ := h.2 k (by omega)
  have hd1 : 1 ≤ d := by
    by_contra hd0
    have hd0 : d = 0 := by omega
    subst hd0
    obtain ⟨p, hp, -⟩ := hd (fun _ => ⟨0, by omega⟩)
    have h01 := (congruent_iff_dist_eq.mp hp) ⟨heptagon r 0, ⟨0, rfl⟩⟩ ⟨heptagon r 1, ⟨1, rfl⟩⟩
    rw [dist_eq_zero_of_fin_zero] at h01
    have h01' : heptagon r 0 = heptagon r 1 := dist_eq_zero.mp h01
    have hx01 := congrArg (fun p : Space 2 => p 0) h01'
    simp at hx01
  refine ⟨d, hd1, fun c => ?_⟩
  obtain ⟨p, hp, i, hi⟩ := hd c
  refine ⟨fun j => p ⟨heptagon r j, ⟨j, rfl⟩⟩, fun j l => ?_, i, fun j => hi _⟩
  exact ((congruent_iff_dist_eq.mp hp) ⟨heptagon r j, ⟨j, rfl⟩⟩ ⟨heptagon r l, ⟨l, rfl⟩⟩).symm

/-- The heptagon's range is not `IsRamsey`, for every transcendental `r > 2`. -/
theorem not_isRamsey (r : ℝ) (hr : 2 < r) (ht : Transcendental ℚ r) :
    ¬ Erdos174.IsRamsey (Set.range (heptagon r)) :=
  fun h => not_ramsey r hr ht (ramsey_of_isRamsey r h)

/-- A transcendental radius above `2`: OpenAI's factorial-series parameter shifted by `2`. -/
def r₀ : ℝ := 2 + GrahamSpherical.parameter

theorem r₀_gt_two : 2 < r₀ := by
  have := GrahamSpherical.parameter_bounds
  unfold r₀
  linarith [this.1]

theorem r₀_transcendental : Transcendental ℚ r₀ := by
  intro h
  apply GrahamSpherical.parameter_transcendental
  have h2 : IsAlgebraic ℚ (2 : ℝ) := by
    simpa using (isAlgebraic_natCast (R := ℚ) (A := ℝ) 2)
  have := h.sub h2
  simpa [r₀] using this

/-- **Graham's conjecture, as stated in formal-conjectures (`erdos_174.variants.graham`), is false**:
the finite cospherical set `range (heptagon r₀)` is not `IsRamsey`. -/
theorem graham_false : ¬ Erdos174.erdos_174.variants.graham.statement :=
  fun h => not_isRamsey r₀ r₀_gt_two r₀_transcendental
    (h (Set.range (heptagon r₀)) (Set.finite_range _) (heptagon_cospherical r₀ r₀_gt_two))

/-- The same, with the statement spelled out. -/
theorem graham_false' :
    ¬ (∀ {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n))), A.Finite →
      EuclideanGeometry.Cospherical A → Erdos174.IsRamsey A) :=
  fun h => graham_false (fun A hA hs => h A hA hs)

end

end HeptagonRamsey.Heptagon
