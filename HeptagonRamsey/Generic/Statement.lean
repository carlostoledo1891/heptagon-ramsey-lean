module

public import HeptagonRamsey.Generic.Seven
public import HeptagonRamsey.Heptagon.Transport

@[expose] public section

/-!
# Theorem A.3 and its seven-point corollary in Mathlib vocabulary

The statements of `generic_seven_not_ramsey` (Theorem A.3 of arXiv:2609.23327, as printed, without
its measure clause) and `seven_circle_configuration` with the seven points `p(tᵢ)` written out in
`EuclideanSpace ℝ (Fin 2)` and "not Ramsey" in formal-conjectures' sense (`Erdos174.IsRamsey`, the
verbatim copy in Transport.lean), for `Challenge.lean`. The transport is
`ramsey_of_isRamsey_range`: for any finite family, formal-conjectures' `IsRamsey` of its range gives
OpenAI's `Ramsey` of the family.
-/

namespace HeptagonRamsey.Generic

open OAI OAI.EuclideanRamsey

noncomputable section

/-- formal-conjectures' `IsRamsey` of the range of a family gives OpenAI's `Ramsey` of the family.
`IsRamsey` allows the dimension `0`; a copy of the range in `ℝ⁰` forces the family to be constant,
and a constant family is Ramsey in OpenAI's sense (one point of `ℝ¹`). -/
theorem ramsey_of_isRamsey_range {s d : ℕ} (a : Fin s → Space d)
    (h : Erdos174.IsRamsey (Set.range a)) : Ramsey a := by
  intro k hk
  obtain ⟨D, hD⟩ := h.2 k (by omega)
  by_cases hD0 : D = 0
  · subst hD0
    obtain ⟨p, hp, -⟩ := hD (fun _ => ⟨0, by omega⟩)
    have hconst : ∀ i j, a i = a j := by
      intro i j
      have hij := (congruent_iff_dist_eq.mp hp) ⟨a i, ⟨i, rfl⟩⟩ ⟨a j, ⟨j, rfl⟩⟩
      rw [HeptagonRamsey.Heptagon.dist_eq_zero_of_fin_zero] at hij
      exact dist_eq_zero.mp hij
    refine ⟨1, le_rfl, fun c => ⟨fun _ => 0, fun i j => ?_, c 0, fun _ => rfl⟩⟩
    show dist (0 : Space 1) 0 = dist (a i) (a j)
    rw [hconst i j, dist_self, dist_self]
  · refine ⟨D, by omega, fun c => ?_⟩
    obtain ⟨p, hp, i, hi⟩ := hD c
    refine ⟨fun j => p ⟨a j, ⟨j, rfl⟩⟩, fun j l => ?_, i, fun j => hi _⟩
    exact ((congruent_iff_dist_eq.mp hp) ⟨a j, ⟨j, rfl⟩⟩ ⟨a l, ⟨l, rfl⟩⟩).symm

/-- **Theorem A.3 of arXiv:2609.23327v1, as printed, without the measure clause**, in Mathlib
vocabulary: for distinct `t₁, t₂, t₃` and `t₄, …, t₇` algebraically independent over
`K = ℚ(t₁, t₂, t₃)`, the set of the seven points `p(tᵢ) = ((1 − tᵢ²)/(1 + tᵢ²), 2tᵢ/(1 + tᵢ²))` is not
Ramsey. Lean indices are the paper's minus one. -/
theorem generic_seven_not_isRamsey (t : Fin 7 → ℝ)
    (h3 : Function.Injective ![t 0, t 1, t 2])
    (h4 : AlgebraicIndependent ↥(IntermediateField.adjoin ℚ ({t 0, t 1, t 2} : Set ℝ))
      ![t 3, t 4, t 5, t 6]) :
    ¬ Erdos174.IsRamsey (Set.range fun i : Fin 7 =>
      !₂[(1 - t i ^ 2) / (1 + t i ^ 2), 2 * t i / (1 + t i ^ 2)]) := by
  intro h
  have hR : Ramsey (circ t) := by
    rw [← literal_eq]
    exact ramsey_of_isRamsey_range (literal t) h
  have e3 : (fun i : Fin 3 => t ⟨i.val, by omega⟩) = ![t 0, t 1, t 2] := by
    funext i; fin_cases i <;> rfl
  have e4 : (fun i : Fin 4 => t ⟨i.val + 3, by omega⟩) = ![t 3, t 4, t 5, t 6] := by
    funext i; fin_cases i <;> rfl
  exact generic_seven_not_ramsey t (e3 ▸ h3) (e4 ▸ h4) hR

/-- **`seven_circle_configuration` in Mathlib vocabulary**: for `t₁, …, t₇` algebraically
independent over `ℚ`, the seven points `p(tᵢ)` are distinct, lie on the unit circle, and their set
is not Ramsey. -/
theorem seven_circle_configuration_isRamsey (t : Fin 7 → ℝ) (ht : AlgebraicIndependent ℚ t) :
    let a : Fin 7 → EuclideanSpace ℝ (Fin 2) := fun i =>
      !₂[(1 - t i ^ 2) / (1 + t i ^ 2), 2 * t i / (1 + t i ^ 2)]
    Function.Injective a ∧ (∀ i, a i ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) ∧
      ¬ Erdos174.IsRamsey (Set.range a) := by
  intro a
  obtain ⟨h1, h2, h3⟩ := seven_circle_configuration t ht
  exact ⟨h1, fun i => Metric.mem_sphere.mpr (h2 i),
    fun h => h3 (ramsey_of_isRamsey_range (literal t) h)⟩

end

end HeptagonRamsey.Generic
