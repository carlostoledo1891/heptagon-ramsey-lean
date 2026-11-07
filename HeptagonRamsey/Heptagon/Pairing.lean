import OAI.Combinatorics.EuclideanRamsey.TensorDescent

/-!
# The derivation pairing on OpenAI's tensor ring

For a configuration `a : Fin s → Space d` and a derivation `D : Derivation ℤ ℝ ℝ`, the ℚ-linear map
`Φ : Coeff a ⊗[ℚ] Coeff a → ℝ`, `x ⊗ y ↦ D x * D y`, with its companions
`Ψ₁ : x ⊗ y ↦ x * D y`, `Ψ₂ : x ⊗ y ↦ D x * y` and `μ : x ⊗ y ↦ x * y`.
The expansion lemma for a sandwich `(x ⊗ 1) * z * (1 ⊗ y)`, and the weighted trace of the
criterion's identity `∑ α β (augmented i α ⊗ 1) P α β (1 ⊗ augmented i β) = 0`.
-/

namespace HeptagonRamsey.Heptagon

open OAI OAI.EuclideanRamsey
open scoped TensorProduct BigOperators

noncomputable section

variable {s d : ℕ} (a : Fin s → Space d) (D : Derivation ℤ ℝ ℝ)

/-- The inclusion of the coordinate field into `ℝ`, as a ℚ-linear map. -/
def incl : Coeff a →ₗ[ℚ] ℝ := (coordinateField a).val.toLinearMap

@[simp] theorem incl_apply (x : Coeff a) : incl a x = (x : ℝ) := rfl

/-- The derivation restricted to the coordinate field, as a ℚ-linear map into `ℝ`. -/
def der : Coeff a →ₗ[ℚ] ℝ where
  toFun x := D (x : ℝ)
  map_add' x y := by simp
  map_smul' q x := by
    simp only [RingHom.id_apply]
    rw [IntermediateField.coe_smul]
    exact map_rat_smul D q (x : ℝ)

@[simp] theorem der_apply (x : Coeff a) : der a D x = D (x : ℝ) := rfl

/-- `x ⊗ y ↦ f x * g y`, extended ℚ-linearly. -/
def pair (f g : Coeff a →ₗ[ℚ] ℝ) : TensorRing a →ₗ[ℚ] ℝ :=
  TensorProduct.lift ((LinearMap.mul ℚ ℝ).compl₁₂ f g)

@[simp] theorem pair_tmul (f g : Coeff a →ₗ[ℚ] ℝ) (x y : Coeff a) :
    pair a f g (x ⊗ₜ[ℚ] y) = f x * g y := by
  simp [pair, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply]

/-- `Φ (x ⊗ y) = D x * D y`. -/
def Φ : TensorRing a →ₗ[ℚ] ℝ := pair a (der a D) (der a D)
/-- `Ψ₁ (x ⊗ y) = x * D y`. -/
def Ψ₁ : TensorRing a →ₗ[ℚ] ℝ := pair a (incl a) (der a D)
/-- `Ψ₂ (x ⊗ y) = D x * y`. -/
def Ψ₂ : TensorRing a →ₗ[ℚ] ℝ := pair a (der a D) (incl a)
/-- `μ (x ⊗ y) = x * y`, the real value of OpenAI's `multiply`. -/
def μ : TensorRing a →ₗ[ℚ] ℝ := pair a (incl a) (incl a)

@[simp] theorem Φ_tmul (x y : Coeff a) : Φ a D (x ⊗ₜ[ℚ] y) = D (x : ℝ) * D (y : ℝ) := by
  simp [Φ]
@[simp] theorem Ψ₁_tmul (x y : Coeff a) : Ψ₁ a D (x ⊗ₜ[ℚ] y) = (x : ℝ) * D (y : ℝ) := by
  simp [Ψ₁]
@[simp] theorem Ψ₂_tmul (x y : Coeff a) : Ψ₂ a D (x ⊗ₜ[ℚ] y) = D (x : ℝ) * (y : ℝ) := by
  simp [Ψ₂]
@[simp] theorem μ_tmul (x y : Coeff a) : μ a (x ⊗ₜ[ℚ] y) = (x : ℝ) * (y : ℝ) := by
  simp [μ]

/-- `μ` is the real value of `multiply`. -/
theorem μ_eq_multiply (z : TensorRing a) : μ a z = ((multiply a z : Coeff a) : ℝ) := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    simp [multiply, Algebra.TensorProduct.lmul'_apply_tmul]
  | add z₁ z₂ h₁ h₂ =>
    rw [map_add, map_add, h₁, h₂, IntermediateField.coe_add]

/-- The expansion of the pairing on a sandwich. -/
theorem Φ_sandwich (x y : Coeff a) (z : TensorRing a) :
    Φ a D ((x ⊗ₜ[ℚ] (1 : Coeff a)) * z * ((1 : Coeff a) ⊗ₜ[ℚ] y)) =
      (x : ℝ) * (y : ℝ) * Φ a D z + (x : ℝ) * D (y : ℝ) * Ψ₂ a D z
        + D (x : ℝ) * (y : ℝ) * Ψ₁ a D z + D (x : ℝ) * D (y : ℝ) * μ a z := by
  induction z using TensorProduct.inductionOn with
  | tmul u v =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    simp only [Φ_tmul, Ψ₁_tmul, Ψ₂_tmul, μ_tmul, one_mul, mul_one,
      IntermediateField.coe_mul, Derivation.leibniz, smul_eq_mul]
    ring
  | add z₁ z₂ h₁ h₂ =>
    rw [mul_add, add_mul, map_add, h₁, h₂, map_add, map_add, map_add, map_add]
    ring

/-- The augmented coordinates of the configuration, as reals. -/
def A (i : Fin s) (α : Option (Fin d)) : ℝ := (augmented a i α : ℝ)

@[simp] theorem A_none (i : Fin s) : A a i none = 1 := by
  simp [A, augmented]

@[simp] theorem A_some (i : Fin s) (j : Fin d) : A a i (some j) = a i j := rfl

/-- Summing the criterion's identity against the weights after applying `Φ`:
the four moment matrices against `Φ`, `Ψ₂`, `Ψ₁`, `μ` of `P`. -/
theorem weighted_trace (lam : Fin s → ℝ)
    (P : Matrix (Option (Fin d)) (Option (Fin d)) (TensorRing a))
    (hP : ∀ i : Fin s, ∑ α, ∑ β,
      ((augmented a i α) ⊗ₜ[ℚ] (1 : Coeff a)) * P α β *
      ((1 : Coeff a) ⊗ₜ[ℚ] (augmented a i β)) = 0) :
    ∑ α, ∑ β,
      ((∑ i, lam i * A a i α * A a i β) * Φ a D (P α β)
        + (∑ i, lam i * A a i α * D (A a i β)) * Ψ₂ a D (P α β)
        + (∑ i, lam i * D (A a i α) * A a i β) * Ψ₁ a D (P α β)
        + (∑ i, lam i * D (A a i α) * D (A a i β)) * μ a (P α β)) = 0 := by
  have h : ∀ i, ∑ α, ∑ β, Φ a D (((augmented a i α) ⊗ₜ[ℚ] (1 : Coeff a)) * P α β *
      ((1 : Coeff a) ⊗ₜ[ℚ] (augmented a i β))) = 0 := by
    intro i
    simp only [← map_sum, hP, map_zero]
  have key : ∀ α β,
      (∑ i, lam i * A a i α * A a i β) * Φ a D (P α β)
        + (∑ i, lam i * A a i α * D (A a i β)) * Ψ₂ a D (P α β)
        + (∑ i, lam i * D (A a i α) * A a i β) * Ψ₁ a D (P α β)
        + (∑ i, lam i * D (A a i α) * D (A a i β)) * μ a (P α β)
      = ∑ i, lam i * Φ a D (((augmented a i α) ⊗ₜ[ℚ] (1 : Coeff a)) * P α β *
          ((1 : Coeff a) ⊗ₜ[ℚ] (augmented a i β))) := by
    intro α β
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Φ_sandwich]
    simp only [A]
    ring
  have swap : ∀ (f : Fin s → Option (Fin d) → Option (Fin d) → ℝ),
      ∑ α, ∑ β, ∑ i, lam i * f i α β = ∑ i, lam i * ∑ α, ∑ β, f i α β := by
    intro f
    calc ∑ α, ∑ β, ∑ i, lam i * f i α β
        = ∑ α, ∑ i, ∑ β, lam i * f i α β :=
          Finset.sum_congr rfl (fun α _ => Finset.sum_comm)
      _ = ∑ i, ∑ α, ∑ β, lam i * f i α β := Finset.sum_comm
      _ = ∑ i, lam i * ∑ α, ∑ β, f i α β := by simp only [Finset.mul_sum]
  simp only [key]
  rw [swap]
  exact Finset.sum_eq_zero fun i _ => by rw [h i, mul_zero]

end

end HeptagonRamsey.Heptagon
