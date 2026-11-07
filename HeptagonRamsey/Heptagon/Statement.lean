module

public import HeptagonRamsey.Heptagon.Transport

@[expose] public section

/-!
# Pálvölgyi's Theorem 1 in Mathlib vocabulary

The seven points written out as a set of `EuclideanSpace ℝ (Fin 2)` (no definition of this
repository or of OpenAI's in the statement), on the circle of centre `(r, 0)` and radius `r`, and
not Ramsey in formal-conjectures' sense (`Erdos174.IsRamsey`, the verbatim copy in
Transport.lean). Added for the Palomar packaging (`Challenge.lean`); the proof is `range_heptagon`
and `not_isRamsey`.
-/

namespace HeptagonRamsey.Heptagon

open OAI OAI.EuclideanRamsey

noncomputable section

/-- `heptagon r`, as a vector of its seven points written out. -/
theorem heptagon_eq_vec (r : ℝ) :
    heptagon r = ![!₂[0, 0], !₂[1, √(2 * r - 1)], !₂[1, -√(2 * r - 1)],
      !₂[3, √(3 * (2 * r - 3))], !₂[3, -√(3 * (2 * r - 3))],
      !₂[4, √(4 * (2 * r - 4))], !₂[4, -√(4 * (2 * r - 4))]] := by
  funext i
  fin_cases i <;> simp [heptagon]

/-- The range of `heptagon r` is the set of its seven points. -/
theorem range_heptagon (r : ℝ) :
    Set.range (heptagon r) =
      ({!₂[0, 0], !₂[1, √(2 * r - 1)], !₂[1, -√(2 * r - 1)],
        !₂[3, √(3 * (2 * r - 3))], !₂[3, -√(3 * (2 * r - 3))],
        !₂[4, √(4 * (2 * r - 4))], !₂[4, -√(4 * (2 * r - 4))]} :
        Set (EuclideanSpace ℝ (Fin 2))) := by
  rw [heptagon_eq_vec]
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

/-- **Pálvölgyi's Theorem 1** (arXiv:2609.23327), in Mathlib vocabulary: for transcendental
`r > 2`, the seven points `(0, 0)` and `(j, ±√(j(2r − j)))`, `j ∈ {1, 3, 4}`, lie on the circle of
centre `(r, 0)` and radius `r`, and they are not Ramsey in formal-conjectures' sense. -/
theorem heptagon_counterexample (r : ℝ) (hr : 2 < r) (ht : Transcendental ℚ r) :
    let S : Set (EuclideanSpace ℝ (Fin 2)) :=
      {!₂[0, 0], !₂[1, √(2 * r - 1)], !₂[1, -√(2 * r - 1)],
        !₂[3, √(3 * (2 * r - 3))], !₂[3, -√(3 * (2 * r - 3))],
        !₂[4, √(4 * (2 * r - 4))], !₂[4, -√(4 * (2 * r - 4))]}
    S ⊆ Metric.sphere !₂[r, 0] r ∧ ¬ Erdos174.IsRamsey S := by
  intro S
  have hS : S = Set.range (heptagon r) := (range_heptagon r).symm
  rw [hS]
  refine ⟨?_, not_isRamsey r hr ht⟩
  rintro p ⟨i, rfl⟩
  exact Metric.mem_sphere.mpr (heptagon_dist_centre r hr i)

end

end HeptagonRamsey.Heptagon
