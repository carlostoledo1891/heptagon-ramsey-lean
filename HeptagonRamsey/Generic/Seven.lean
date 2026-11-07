import HeptagonRamsey.Generic.A3

/-!
# Amendment D: the ℚ-independence corollary of Theorem A.3, in the shape of OpenAI's nine-point statement

OpenAI's `OAI.EuclideanRamsey.NineStatement.nine_circle_configuration` (openai/math 4eaee875,
lean/OAI/Combinatorics/EuclideanRamsey/NineStatement.lean, and the Comparator challenge
ComparatorChallenges/EuclideanRamseyNine.lean): nine points of the unit circle in their literal rational
parametrisation `literalCircleConfig`, with parameters algebraically independent over `ℚ`, are distinct, on the unit
circle, and not Ramsey. Here the same statement for SEVEN points. `literal` is their `literalCircleConfig` with
`Fin 9` replaced by `Fin 7`, and the statement is theirs with the same replacement (both checked token for token
against the pinned files by d/verbatim_seven.py).

The proof is Theorem A.3 (`generic_seven_not_ramsey`, HeptagonRamsey/Generic/A3.lean), not a second proof of it: the
`ℚ`-independence of all seven parameters gives the distinctness of `t₁, t₂, t₃` (`AlgebraicIndependent.injective`)
and the independence of `t₄, …, t₇` over `K = ℚ(t₁, t₂, t₃)` (Mathlib's `AlgebraicIndependent.adjoin_of_disjoint`,
over the subalgebra `Algebra.adjoin ℚ {t₁, t₂, t₃}`, moved to the intermediate field by
`IntermediateField.algebraicIndependent_adjoin_iff`). `literal t = circ t` as in their `literalCircleConfig_eq`.
-/

namespace HeptagonRamsey.Generic

open OAI OAI.EuclideanRamsey

noncomputable section

-- BEGIN VERBATIM (OpenAI's NineStatement.literalCircleConfig, `Fin 9` → `Fin 7`)
/-- The rational parametrization of seven points in the Euclidean plane. -/
def literal (t : Fin 7 → ℝ) (i : Fin 7) : Space 2 :=
  WithLp.toLp 2 ![(1 - (t i)^2) / (1 + (t i)^2),
    (2 * t i) / (1 + (t i)^2)]
-- END VERBATIM

/-- Their `literalCircleConfig_eq`, for seven points: the literal parametrisation is `circ`
(OpenAI's `NineGeometry.circlePoint`). -/
theorem literal_eq (t : Fin 7 → ℝ) : literal t = circ t := by
  funext i
  ext j
  fin_cases j <;>
    simp [literal, circ]

/-- `t₁, t₂, t₃` are distinct (A.3's first hypothesis). -/
theorem lo_injective_of_independent (t : Fin 7 → ℝ) (ht : AlgebraicIndependent ℚ t) :
    Function.Injective (fun i : Fin 3 => t ⟨i.val, by omega⟩) := by
  intro i j h
  exact Fin.ext (Fin.mk.inj_iff.mp (ht.injective h))

/-- The images of `{0, 1, 2}`: `t '' {0, 1, 2} = {t₁, t₂, t₃}`. -/
theorem image_lo (t : Fin 7 → ℝ) : t '' ({0, 1, 2} : Set (Fin 7)) = {t 0, t 1, t 2} := by
  simp only [Set.image_insert_eq, Set.image_singleton]

theorem disjoint_lo_hi : Disjoint ({0, 1, 2} : Set (Fin 7)) {3, 4, 5, 6} := by
  rw [Set.disjoint_left]
  intro a ha hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with h | h | h | h <;> exact absurd h (by decide)

theorem hi_mem (k : Fin 4) : hi k ∈ ({3, 4, 5, 6} : Set (Fin 7)) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  fin_cases k <;> decide

/-- `t₄, …, t₇` are algebraically independent over `K = ℚ(t₁, t₂, t₃)` (A.3's second hypothesis). -/
theorem hi_independent_of_independent (t : Fin 7 → ℝ) (ht : AlgebraicIndependent ℚ t) :
    AlgebraicIndependent (↥(baseField t)) (fun i : Fin 4 => t ⟨i.val + 3, by omega⟩) := by
  have h := ht.adjoin_of_disjoint disjoint_lo_hi
  rw [image_lo] at h
  have hK : AlgebraicIndependent (↥(baseField t)) (fun i : ↥({3, 4, 5, 6} : Set (Fin 7)) => t i) :=
    IntermediateField.algebraicIndependent_adjoin_iff.mpr h
  refine hK.comp (fun k => ⟨hi k, hi_mem k⟩) ?_
  intro k l hkl
  have hv := congrArg (fun x : ↥({3, 4, 5, 6} : Set (Fin 7)) => (x : Fin 7).val) hkl
  simp only [hi] at hv
  exact Fin.ext (by omega)

-- BEGIN VERBATIM (OpenAI's NineStatement.nine_circle_configuration, `Fin 9` → `Fin 7`, names as above)
/-- Seven points on the unit circle form a non-Ramsey configuration when their
parameters are algebraically independent over the rationals. -/
theorem seven_circle_configuration (t : Fin 7 → ℝ)
    (ht : AlgebraicIndependent ℚ t) :
    Function.Injective (literal t) ∧
      (∀ i, dist (literal t i) 0 = 1) ∧
      ¬ Ramsey (literal t) := by
-- END VERBATIM
  rw [literal_eq]
  exact ⟨NineGeometry.circlePoint_injective.comp ht.injective,
    fun i => NineGeometry.circlePoint_on_circle (t i),
    generic_seven_not_ramsey t (lo_injective_of_independent t ht) (hi_independent_of_independent t ht)⟩

end

end HeptagonRamsey.Generic
