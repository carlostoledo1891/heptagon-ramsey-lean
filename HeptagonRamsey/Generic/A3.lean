module

public import HeptagonRamsey.Generic.Derivation
public import HeptagonRamsey.Generic.Moments
public import HeptagonRamsey.Generic.LemmaA1
public import OAI.Combinatorics.EuclideanRamsey.TensorDescent

@[expose] public section

/-!
# Theorem A.3 of arXiv:2609.23327v1 (app:thm:generic): the generic seven points on a circle are not Ramsey

"Fix three distinct real numbers `t₁, t₂, t₃`. If `t₄, t₅, t₆, t₇` are algebraically independent over
`K = ℚ(t₁, t₂, t₃)`, then `{p(t₁), …, p(t₇)}` is not Ramsey." (.tex 390–398; Lean indices are the paper's minus one.)
The measure clause ("consequently almost every seven-point subset of a fixed circle is not Ramsey") is not part of
this statement, as in OpenAI's nine-point `NineStatement.nine_circle_configuration`, which assumes the independence
itself. `Ramsey` and `FieldCriterion` are OpenAI's (EuclideanRamsey/Model.lean), `ramsey_fieldCriterion` is their
necessity theorem (TensorDescent.lean), `circle_five_affineSpan` is theirs (CircleSpan.lean).
-/

namespace HeptagonRamsey.Generic

open OAI OAI.EuclideanRamsey
open scoped BigOperators

noncomputable section

/-- `K = ℚ(t₁, t₂, t₃)`. -/
def baseField (t : Fin 7 → ℝ) : IntermediateField ℚ ℝ := IntermediateField.adjoin ℚ {t 0, t 1, t 2}

/-- The paper's `t₁, t₂, t₃`. -/
def lo (i : Fin 3) : Fin 7 := ⟨i.val, by omega⟩
/-- The paper's `t₄, …, t₇`. -/
def hi (k : Fin 4) : Fin 7 := ⟨k.val + 3, by omega⟩

theorem lo_or_hi (i : Fin 7) : (∃ a, i = lo a) ∨ ∃ k, i = hi k := by
  by_cases h : i.val < 3
  · exact Or.inl ⟨⟨i.val, h⟩, rfl⟩
  · exact Or.inr ⟨⟨i.val - 3, by omega⟩, Fin.ext (by simp only [hi]; omega)⟩

theorem mem_baseField_lo (t : Fin 7 → ℝ) (a : Fin 3) : t (lo a) ∈ baseField t := by
  apply IntermediateField.subset_adjoin
  fin_cases a <;> simp [lo]

theorem g_lo (t : Fin 7 → ℝ) (a : Fin 3) : g t (t (lo a)) = 0 := by
  fin_cases a <;> simp [lo, g]

/-- The seven parameters are distinct: `t₁, t₂, t₃` by hypothesis, `t₄..t₇` by independence, and no `t_k`
(`k ≥ 4`) lies in `K`, being transcendental over it. -/
theorem injective_of_generic (t : Fin 7 → ℝ)
    (h3 : Function.Injective (fun i : Fin 3 => t ⟨i.val, by omega⟩))
    (h4 : AlgebraicIndependent (↥(baseField t)) (fun i : Fin 4 => t ⟨i.val + 3, by omega⟩)) :
    Function.Injective t := by
  have cross : ∀ (a : Fin 3) (k : Fin 4), t (hi k) ≠ t (lo a) := by
    intro a k h
    apply h4.transcendental k
    change IsAlgebraic (↥(baseField t)) (t (hi k))
    rw [h]
    exact isAlgebraic_algebraMap (⟨t (lo a), mem_baseField_lo t a⟩ : baseField t)
  intro i j hij
  rcases lo_or_hi i with ⟨a, rfl⟩ | ⟨k, rfl⟩ <;> rcases lo_or_hi j with ⟨b, rfl⟩ | ⟨l, rfl⟩
  · rw [h3 hij]
  · exact absurd hij.symm (cross a l)
  · exact absurd hij (cross b k)
  · rw [h4.injective hij]

/-- The derivation of the proof: zero on `K`, `D(t_i) = g(t_i)` for the four independent parameters, hence
`D(t_i) = g(t_i)` at all seven (`g` vanishes at `t₁, t₂, t₃`). -/
theorem exists_derivation_g (t : Fin 7 → ℝ)
    (h4 : AlgebraicIndependent (↥(baseField t)) (fun i : Fin 4 => t ⟨i.val + 3, by omega⟩)) :
    ∃ D : Derivation ℤ ℝ ℝ, ∀ i, D (t i) = g t (t i) := by
  obtain ⟨D, hDK, hDb⟩ := exists_derivation_vanishing_prescribed (baseField t) _ h4
    (fun k => g t (t (hi k)))
  refine ⟨D, fun i => ?_⟩
  rcases lo_or_hi i with ⟨a, rfl⟩ | ⟨k, rfl⟩
  · rw [hDK _ (mem_baseField_lo t a), g_lo]
  · exact hDb k

/-- The seven points affinely span the plane (OpenAI's `circle_five_affineSpan` on the first five). -/
theorem circ_affineSpan (t : Fin 7 → ℝ) (ht : Function.Injective t) :
    affineSpan ℝ (Set.range (circ t)) = ⊤ := by
  let f5 : Fin 5 → Fin 7 := fun i => ⟨i.val, by omega⟩
  have hf5 : Function.Injective f5 := fun i j h => Fin.ext (by simpa [f5] using congrArg Fin.val h)
  have hfive : affineSpan ℝ (Set.range (circ t ∘ f5)) = ⊤ :=
    CircleConsequence.circle_five_affineSpan (circ t ∘ f5)
      (NineGeometry.circlePoint_injective.comp (ht.comp hf5)) 0 1
      (fun i => NineGeometry.circlePoint_on_circle (t (f5 i)))
  apply top_unique
  rw [← hfive]
  apply affineSpan_mono
  rintro p ⟨i, rfl⟩
  exact Set.mem_range_self (f5 i)

/-- The generic seven points fail OpenAI's `FieldCriterion`: Lemma A.1 (symmetric form) with the weights
`λ_i = (1+t_i²)²/H'(t_i)` and the derivation `D(t_i) = g(t_i)`, energy `E = 4`. -/
theorem not_fieldCriterion_generic (t : Fin 7 → ℝ)
    (h3 : Function.Injective (fun i : Fin 3 => t ⟨i.val, by omega⟩))
    (h4 : AlgebraicIndependent (↥(baseField t)) (fun i : Fin 4 => t ⟨i.val + 3, by omega⟩)) :
    ¬ FieldCriterion (circ t) := by
  obtain ⟨D, hD⟩ := exists_derivation_g t h4
  have ht := injective_of_generic t h3 h4
  exact not_fieldCriterion_of_moments (circ t) D (weight t) (moment_one ht) (moment_lin ht)
    (moment_quad ht) (moment_D D hD ht) (moment_M D hD ht) (by rw [energy D hD ht]; norm_num)

/-- **Theorem A.3 of arXiv:2609.23327v1 (Pálvölgyi), as printed, without the measure clause.**
For distinct `t₁, t₂, t₃` and `t₄, …, t₇` algebraically independent over `K = ℚ(t₁, t₂, t₃)`, the seven points
`p(t_i) = ((1−t_i²)/(1+t_i²), 2t_i/(1+t_i²))` are not Ramsey (OpenAI's `Ramsey`). -/
theorem generic_seven_not_ramsey (t : Fin 7 → ℝ)
    (h3 : Function.Injective (fun i : Fin 3 => t ⟨i.val, by omega⟩))
    (h4 : AlgebraicIndependent (↥(baseField t)) (fun i : Fin 4 => t ⟨i.val + 3, by omega⟩)) :
    ¬ Ramsey (circ t) := fun hR =>
  not_fieldCriterion_generic t h3 h4
    (ramsey_fieldCriterion (circ t) (by norm_num) (circ_affineSpan t (injective_of_generic t h3 h4)) hR)

end

end HeptagonRamsey.Generic
