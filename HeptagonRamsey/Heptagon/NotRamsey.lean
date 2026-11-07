module

public import HeptagonRamsey.Heptagon.Criterion
public import OAI.Combinatorics.EuclideanRamsey.CircleSpan

@[expose] public section

/-!
# The heptagon is not Ramsey, through OpenAI's classification

`affineSpan ℝ (range (heptagon r)) = ⊤` (three of the first five points already span the plane, by their
`circle_five_affineSpan`), then `ramsey_fieldCriterion` turns `¬ FieldCriterion` into `¬ Ramsey`.
-/

namespace HeptagonRamsey.Heptagon

open OAI OAI.EuclideanRamsey

noncomputable section

/-- The centre `(r, 0)` of the circle through the seven points. -/
def centre (r : ℝ) : Space 2 := WithLp.toLp 2 ![r, 0]

@[simp] theorem centre_apply_zero (r : ℝ) : centre r 0 = r := rfl
@[simp] theorem centre_apply_one (r : ℝ) : centre r 1 = 0 := rfl

/-- Every point of the heptagon is at distance `r` from `(r, 0)`. -/
theorem heptagon_dist_centre (r : ℝ) (hr : 2 < r) (i : Fin 7) :
    dist (heptagon r i) (centre r) = r := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  change Real.sqrt (dist (heptagon r i 0) (centre r 0) ^ 2 + dist (heptagon r i 1) (centre r 1) ^ 2) = r
  simp only [heptagon_apply_zero, heptagon_apply_one, centre_apply_zero, centre_apply_one,
    Real.dist_eq, sq_abs]
  have h := hy_mul_self r hr i
  rw [show (hx i - r) ^ 2 + (hy r i - 0) ^ 2 = r ^ 2 by linear_combination h]
  exact Real.sqrt_sq (by linarith)

theorem heptagon_cospherical (r : ℝ) (hr : 2 < r) :
    EuclideanGeometry.Cospherical (Set.range (heptagon r)) :=
  ⟨centre r, r, by rintro p ⟨i, rfl⟩; exact heptagon_dist_centre r hr i⟩

/-- The first five points. -/
def firstFive (i : Fin 5) : Fin 7 := ⟨i.val, by omega⟩

theorem firstFive_heptagon_injective (r : ℝ) (hr : 2 < r) :
    Function.Injective (heptagon r ∘ firstFive) := by
  have hs1 : 0 < Real.sqrt (2 * r - 1) := Real.sqrt_pos.mpr (by linarith)
  have hs3 : 0 < Real.sqrt (3 * (2 * r - 3)) := Real.sqrt_pos.mpr (by linarith)
  intro i j h
  have h0 := congrArg (fun p : Space 2 => p 0) h
  have h1 := congrArg (fun p : Space 2 => p 1) h
  simp only [Function.comp_apply, heptagon_apply_zero, heptagon_apply_one] at h0 h1
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.reduceFinMk, Fin.isValue, firstFive, hx_0, hx_1, hx_2, hx_3, hx_4,
      hy_0, hy_1, hy_2, hy_3, hy_4] at h0 h1 ⊢ <;>
    first | rfl | (exfalso; linarith)

/-- The seven points affinely span the plane. -/
theorem heptagon_affineSpan (r : ℝ) (hr : 2 < r) :
    affineSpan ℝ (Set.range (heptagon r)) = ⊤ := by
  have hfive : affineSpan ℝ (Set.range (heptagon r ∘ firstFive)) = ⊤ :=
    CircleConsequence.circle_five_affineSpan (heptagon r ∘ firstFive)
      (firstFive_heptagon_injective r hr) (centre r) r
      (fun i => heptagon_dist_centre r hr (firstFive i))
  apply top_unique
  rw [← hfive]
  apply affineSpan_mono
  rintro p ⟨i, rfl⟩
  exact Set.mem_range_self (firstFive i)

/-- **Pálvölgyi's heptagon is not Euclidean Ramsey** (OpenAI's `Ramsey`), for every transcendental
`r > 2`, through their `ramsey_fieldCriterion`. -/
theorem not_ramsey (r : ℝ) (hr : 2 < r) (ht : Transcendental ℚ r) : ¬ Ramsey (heptagon r) :=
  fun hR => not_fieldCriterion r hr ht
    (ramsey_fieldCriterion (heptagon r) (by norm_num) (heptagon_affineSpan r hr) hR)

end

end HeptagonRamsey.Heptagon
