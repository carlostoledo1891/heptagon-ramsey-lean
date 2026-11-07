module

public import HeptagonRamsey.Heptagon.Pairing

@[expose] public section

/-!
# Lemma A.1 of arXiv:2609.23327v1 in OpenAI's `FieldCriterion` form, with `M` symmetric

The appendix's Lemma A.1 (.tex 264–292): real weights `λ_i` and a derivation `D` with
`Σλ = 0`, `Σλ p = 0`, `Σλ p pᵀ = 0`, `Σλ D(p) = 0`, `M = Σλ D(p) pᵀ` symmetric and `E = Σλ ‖D(p)‖² ≠ 0`
make `P` not Ramsey. Here the conclusion is `¬ FieldCriterion a` (OpenAI's Model.lean), which
`TensorDescent.ramsey_fieldCriterion` turns into `¬ Ramsey a` for a spanning configuration.

The proof is H2's weighted trace (HeptagonRamsey/Heptagon/Pairing.lean) with one new lemma: `Ψ₁ + Ψ₂ = D ∘ μ` on the tensor
ring (Leibniz), so on the spatial block of a criterion matrix, where `multiply (P j k) = δ_{jk}` is constant,
`Ψ₂ (P j k) = −Ψ₁ (P j k)`, and the two mixed terms combine to `(M_{jk} − M_{kj}) Ψ₁ (P j k) = 0` — the paper's
"`D(A)ᵀA` is skew-symmetric and `M` is symmetric", transported from isometries to `P`. The constant row and column
vanish by `Σλ D(p) = 0` and `D 1 = 0`. What is left is `Σ_j Σλ D(p_j)² · multiply (P j j) = E`.
-/

namespace HeptagonRamsey.Generic

open OAI OAI.EuclideanRamsey
open HeptagonRamsey.Heptagon (A A_none A_some Φ Ψ₁ Ψ₂ μ Ψ₁_tmul Ψ₂_tmul μ_tmul μ_eq_multiply weighted_trace)
open scoped TensorProduct BigOperators

noncomputable section

variable {s d : ℕ} (a : Fin s → Space d) (D : Derivation ℤ ℝ ℝ)

/-- **Leibniz on the tensor ring**: `Ψ₁ + Ψ₂ = D ∘ μ`. -/
theorem Ψ₁_add_Ψ₂ (z : TensorRing a) : Ψ₁ a D z + Ψ₂ a D z = D (μ a z) := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    rw [Ψ₁_tmul, Ψ₂_tmul, μ_tmul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    ring
  | add z₁ z₂ h₁ h₂ =>
    rw [map_add, map_add, map_add, map_add, ← h₁, ← h₂]
    ring

/-- On the spatial block of a criterion matrix, `μ (P j k) = δ_{jk}`. -/
theorem μ_spatial (P : Matrix (Option (Fin d)) (Option (Fin d)) (TensorRing a))
    (hmul : ∀ α β : Fin d, multiply a (P (some α) (some β)) = if α = β then 1 else 0) (j k : Fin d) :
    μ a (P (some j) (some k)) = if j = k then 1 else 0 := by
  rw [μ_eq_multiply, hmul j k]
  split_ifs <;> simp

/-- On the spatial block of a criterion matrix, `Ψ₂ = −Ψ₁`. -/
theorem Ψ₂_spatial (P : Matrix (Option (Fin d)) (Option (Fin d)) (TensorRing a))
    (hmul : ∀ α β : Fin d, multiply a (P (some α) (some β)) = if α = β then 1 else 0) (j k : Fin d) :
    Ψ₂ a D (P (some j) (some k)) = -Ψ₁ a D (P (some j) (some k)) := by
  have h := Ψ₁_add_Ψ₂ a D (P (some j) (some k))
  have h0 : D (μ a (P (some j) (some k))) = 0 := by
    rw [μ_spatial a P hmul j k]
    split_ifs
    · exact D.map_one_eq_zero
    · exact D.map_zero
  rw [h0] at h
  linarith

theorem D_A_none' (i : Fin s) : D (A a i none) = 0 := by
  rw [A_none]; exact D.map_one_eq_zero

/-- **Lemma A.1, symmetric form, as `¬ FieldCriterion`.** `M = Σλ D(p) pᵀ` need only be symmetric. -/
theorem not_fieldCriterion_of_moments (lam : Fin s → ℝ)
    (h0 : ∑ i, lam i = 0)
    (h1 : ∀ j, ∑ i, lam i * a i j = 0)
    (h2 : ∀ j k, ∑ i, lam i * a i j * a i k = 0)
    (hD1 : ∀ j, ∑ i, lam i * D (a i j) = 0)
    (hM : ∀ j k, ∑ i, lam i * D (a i j) * a i k = ∑ i, lam i * D (a i k) * a i j)
    (hE : ∑ j, ∑ i, lam i * D (a i j) * D (a i j) ≠ 0) :
    ¬ FieldCriterion a := by
  rintro ⟨P, hP, hmul⟩
  have h := weighted_trace a D lam P hP
  -- the ordinary moments, in the augmented (`Option`) indexing
  have m0 : ∀ α β, ∑ i, lam i * A a i α * A a i β = 0 := by
    rintro (_ | j) (_ | k)
    · simpa [A_none] using h0
    · simpa [A_none, A_some] using h1 k
    · simpa [A_none, A_some] using h1 j
    · simpa [A_some] using h2 j k
  have hDn := D_A_none' a D
  -- the constant row and column of the mixed matrices
  have nl : ∀ β, ∑ i, lam i * A a i none * D (A a i β) = 0 := by
    rintro (_ | k)
    · simp only [hDn, mul_zero, Finset.sum_const_zero]
    · simp only [A_none, A_some, mul_one]; exact hD1 k
  have nr : ∀ α, ∑ i, lam i * A a i α * D (A a i none) = 0 := by
    intro α; simp only [hDn, mul_zero, Finset.sum_const_zero]
  have n'l : ∀ β, ∑ i, lam i * D (A a i none) * A a i β = 0 := by
    intro β; simp only [hDn, mul_zero, zero_mul, Finset.sum_const_zero]
  have n'r : ∀ α, ∑ i, lam i * D (A a i α) * A a i none = 0 := by
    rintro (_ | j)
    · simp only [hDn, mul_zero, zero_mul, Finset.sum_const_zero]
    · simp only [A_none, A_some, mul_one]; exact hD1 j
  -- the spatial block of the two mixed matrices agrees, by the symmetry of `M`
  have nn' : ∀ j k : Fin d, ∑ i, lam i * A a i (some j) * D (A a i (some k)) =
      ∑ i, lam i * D (A a i (some j)) * A a i (some k) := by
    intro j k
    simp only [A_some]
    rw [show ∑ i, lam i * a i j * D (a i k) = ∑ i, lam i * D (a i k) * a i j from
      Finset.sum_congr rfl fun i _ => by ring, hM k j]
  -- every term of the weighted trace reduces to its `μ` term
  have hterm : ∀ α β,
      (∑ i, lam i * A a i α * A a i β) * Φ a D (P α β)
        + (∑ i, lam i * A a i α * D (A a i β)) * Ψ₂ a D (P α β)
        + (∑ i, lam i * D (A a i α) * A a i β) * Ψ₁ a D (P α β)
        + (∑ i, lam i * D (A a i α) * D (A a i β)) * μ a (P α β)
      = (∑ i, lam i * D (A a i α) * D (A a i β)) * μ a (P α β) := by
    rintro (_ | j) (_ | k)
    · rw [m0, nl, n'l]; ring
    · rw [m0, nl, n'l]; ring
    · rw [m0, nr, n'r]; ring
    · rw [m0, nn' j k, Ψ₂_spatial a D P hmul j k]; ring
  simp only [hterm] at h
  -- the `μ` terms: the constant row and column vanish, the spatial block is `δ_{jk}`
  have hsum : ∑ α, ∑ β, (∑ i, lam i * D (A a i α) * D (A a i β)) * μ a (P α β) =
      ∑ j, ∑ i, lam i * D (a i j) * D (a i j) := by
    rw [Fintype.sum_option]
    have hrow : ∑ β, (∑ i, lam i * D (A a i none) * D (A a i β)) * μ a (P none β) = 0 :=
      Finset.sum_eq_zero fun β _ => by
        simp only [hDn, mul_zero, zero_mul, Finset.sum_const_zero]
    rw [hrow, zero_add]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fintype.sum_option]
    simp only [hDn, mul_zero, Finset.sum_const_zero, zero_mul, zero_add, μ_spatial a P hmul j,
      mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp [A_some]
  rw [hsum] at h
  exact hE h

end

end HeptagonRamsey.Generic
