import HeptagonRamsey.Heptagon.Pairing
import HeptagonRamsey.Heptagon.Points

/-!
# The heptagon fails OpenAI's `FieldCriterion`

The four weighted moment matrices of the heptagon against a derivation `D` with `D r = 1`:
`Σλ A Aᵀ = 0`, `Σλ A (DA)ᵀ = 0`, `Σλ (DA) Aᵀ = 0`, and `Σλ (DA)(DA)ᵀ` supported on the `(y, y)` entry,
where it equals `E r = −4/(2r−1) + 12/(2r−3) − 8/(2r−4) = −24/((2r−1)(2r−3)(2r−4)) ≠ 0`.
With the weighted trace of the criterion's identity this forces `E r · multiply (P (some 1) (some 1)) = 0`,
against `multiply (P (some 1) (some 1)) = 1`.
-/

namespace HeptagonRamsey.Heptagon

open OAI OAI.EuclideanRamsey
open scoped TensorProduct BigOperators

noncomputable section

/-- The energy `Σλ ‖D p‖²`, as the paper writes it. -/
def E (r : ℝ) : ℝ := -4 / (2 * r - 1) + 12 / (2 * r - 3) - 8 / (2 * r - 4)

theorem E_mul (r : ℝ) (hr : 2 < r) : E r * ((2 * r - 1) * (2 * r - 3) * (2 * r - 4)) = -24 := by
  have h1 : (2 * r - 1 : ℝ) ≠ 0 := by linarith
  have h3 : (2 * r - 3 : ℝ) ≠ 0 := by linarith
  have h4 : (2 * r - 4 : ℝ) ≠ 0 := by linarith
  unfold E
  field_simp
  ring

theorem E_ne_zero (r : ℝ) (hr : 2 < r) : E r ≠ 0 := by
  intro h
  have := E_mul r hr
  rw [h, zero_mul] at this
  norm_num at this

section Moments

variable (r : ℝ) (D : Derivation ℤ ℝ ℝ)

@[simp] theorem A_heptagon_zero (i : Fin 7) : A (heptagon r) i (some 0) = hx i := rfl
@[simp] theorem A_heptagon_one (i : Fin 7) : A (heptagon r) i (some 1) = hy r i := rfl

/-- `Σλ = 0`, `Σλ p = 0`, `Σλ p pᵀ = 0`. -/
theorem moment0 (hr : 2 < r) :
    ∀ α β : Option (Fin 2), ∑ i, lam i * A (heptagon r) i α * A (heptagon r) i β = 0
  | none, none => by
    simp only [Fin.sum_univ_seven, A_none, lam_0, lam_1, lam_2, lam_3, lam_4, lam_5, lam_6]; norm_num
  | none, some 0 => by
    simp only [Fin.sum_univ_seven, A_none, A_heptagon_zero, lam_0, lam_1, lam_2, lam_3, lam_4, lam_5,
      lam_6, hx_0, hx_1, hx_2, hx_3, hx_4, hx_5, hx_6]; norm_num
  | none, some 1 => by
    simp only [Fin.sum_univ_seven, A_none, A_heptagon_one, lam_0, lam_1, lam_2, lam_3, lam_4, lam_5,
      lam_6, hy_0, hy_1, hy_2, hy_3, hy_4, hy_5, hy_6]; ring
  | some 0, none => by
    simp only [Fin.sum_univ_seven, A_none, A_heptagon_zero, lam_0, lam_1, lam_2, lam_3, lam_4, lam_5,
      lam_6, hx_0, hx_1, hx_2, hx_3, hx_4, hx_5, hx_6]; norm_num
  | some 0, some 0 => by
    simp only [Fin.sum_univ_seven, A_heptagon_zero, lam_0, lam_1, lam_2, lam_3, lam_4, lam_5,
      lam_6, hx_0, hx_1, hx_2, hx_3, hx_4, hx_5, hx_6]; norm_num
  | some 0, some 1 => by
    simp only [Fin.sum_univ_seven, A_heptagon_zero, A_heptagon_one, lam_0, lam_1, lam_2, lam_3, lam_4,
      lam_5, lam_6, hx_0, hx_1, hx_2, hx_3, hx_4, hx_5, hx_6, hy_0, hy_1, hy_2, hy_3, hy_4, hy_5, hy_6]
    ring
  | some 1, none => by
    simp only [Fin.sum_univ_seven, A_none, A_heptagon_one, lam_0, lam_1, lam_2, lam_3, lam_4, lam_5,
      lam_6, hy_0, hy_1, hy_2, hy_3, hy_4, hy_5, hy_6]; ring
  | some 1, some 0 => by
    simp only [Fin.sum_univ_seven, A_heptagon_zero, A_heptagon_one, lam_0, lam_1, lam_2, lam_3, lam_4,
      lam_5, lam_6, hx_0, hx_1, hx_2, hx_3, hx_4, hx_5, hx_6, hy_0, hy_1, hy_2, hy_3, hy_4, hy_5, hy_6]
    ring
  | some 1, some 1 => by
    have e1 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 * r - 1 by linarith)
    have e3 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 3 * (2 * r - 3) by linarith)
    have e4 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 4 * (2 * r - 4) by linarith)
    simp only [Fin.sum_univ_seven, A_heptagon_one, lam_0, lam_1, lam_2, lam_3, lam_4, lam_5, lam_6,
      hy_0, hy_1, hy_2, hy_3, hy_4, hy_5, hy_6]
    linear_combination (-4 : ℝ) * e1 + 4 * e3 + (-2 : ℝ) * e4

/-- The derivative of the augmented coordinates is supported on the `y` coordinate. -/
theorem D_A_none (i : Fin 7) : D (A (heptagon r) i none) = 0 := by
  rw [A_none]; exact D.map_one_eq_zero
theorem D_A_zero (i : Fin 7) : D (A (heptagon r) i (some 0)) = 0 := by
  rw [A_heptagon_zero]; exact D_hx D i

/-- `Σλ D(p) = 0`, `Σλ p D(p)ᵀ = 0` (and the constant row, by `D 1 = 0`). -/
theorem moment1 (hr : 2 < r) (hD : D r = 1) :
    ∀ α β : Option (Fin 2), ∑ i, lam i * A (heptagon r) i α * D (A (heptagon r) i β) = 0
  | _, none => by simp only [D_A_none, mul_zero, Finset.sum_const_zero]
  | _, some 0 => by simp only [D_A_zero, mul_zero, Finset.sum_const_zero]
  | none, some 1 => by
    simp only [Fin.sum_univ_seven, A_none, A_heptagon_one, D_hy_zero, D_hy D r hr hD 1 (by decide),
      D_hy D r hr hD 2 (by decide), D_hy D r hr hD 3 (by decide), D_hy D r hr hD 4 (by decide),
      D_hy D r hr hD 5 (by decide), D_hy D r hr hD 6 (by decide)]
    simp only [lam_0, lam_1, lam_2, lam_3, lam_4, lam_5, lam_6, hx_1, hx_2, hx_3, hx_4, hx_5, hx_6,
      hy_1, hy_2, hy_3, hy_4, hy_5, hy_6]
    ring
  | some 0, some 1 => by
    simp only [Fin.sum_univ_seven, A_heptagon_zero, A_heptagon_one, D_hy_zero,
      D_hy D r hr hD 1 (by decide), D_hy D r hr hD 2 (by decide), D_hy D r hr hD 3 (by decide),
      D_hy D r hr hD 4 (by decide), D_hy D r hr hD 5 (by decide), D_hy D r hr hD 6 (by decide)]
    simp only [lam_0, lam_1, lam_2, lam_3, lam_4, lam_5, lam_6, hx_0, hx_1, hx_2, hx_3, hx_4, hx_5,
      hx_6, hy_1, hy_2, hy_3, hy_4, hy_5, hy_6]
    ring
  | some 1, some 1 => by
    have key : ∀ i, lam i * A (heptagon r) i (some 1) * D (A (heptagon r) i (some 1)) = lam i * hx i := by
      intro i
      rw [A_heptagon_one, mul_assoc, hy_mul_D_hy D r hr hD i]
    simp only [key, Fin.sum_univ_seven, lam_0, lam_1, lam_2, lam_3, lam_4, lam_5, lam_6,
      hx_0, hx_1, hx_2, hx_3, hx_4, hx_5, hx_6]
    norm_num

/-- The transpose of `moment1`. -/
theorem moment1' (hr : 2 < r) (hD : D r = 1) :
    ∀ α β : Option (Fin 2), ∑ i, lam i * D (A (heptagon r) i α) * A (heptagon r) i β = 0 := by
  intro α β
  rw [← moment1 r D hr hD β α]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- `Σλ D(p) D(p)ᵀ` is supported on the `(y, y)` entry, where it is `E r`. -/
theorem moment2 (hr : 2 < r) (hD : D r = 1) :
    ∀ α β : Option (Fin 2), ∑ i, lam i * D (A (heptagon r) i α) * D (A (heptagon r) i β) =
      if α = some 1 ∧ β = some 1 then E r else 0
  | none, _ => by simp only [D_A_none, zero_mul, mul_zero, Finset.sum_const_zero]; simp
  | some 0, _ => by simp only [D_A_zero, zero_mul, mul_zero, Finset.sum_const_zero]; simp
  | some 1, none => by simp only [D_A_none, mul_zero, Finset.sum_const_zero]; simp
  | some 1, some 0 => by simp only [D_A_zero, mul_zero, Finset.sum_const_zero]; simp
  | some 1, some 1 => by
    rw [ite_eq_left ⟨rfl, rfl⟩]
    have e1 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 * r - 1 by linarith)
    have e3 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 3 * (2 * r - 3) by linarith)
    have e4 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 4 * (2 * r - 4) by linarith)
    have h1 : (2 * r - 1 : ℝ) ≠ 0 := by linarith
    have h3 : (3 * (2 * r - 3) : ℝ) ≠ 0 := by linarith
    have h4 : (4 * (2 * r - 4) : ℝ) ≠ 0 := by linarith
    simp only [Fin.sum_univ_seven, A_heptagon_one, D_hy_zero, D_hy D r hr hD 1 (by decide),
      D_hy D r hr hD 2 (by decide), D_hy D r hr hD 3 (by decide), D_hy D r hr hD 4 (by decide),
      D_hy D r hr hD 5 (by decide), D_hy D r hr hD 6 (by decide)]
    simp only [lam_0, lam_1, lam_2, lam_3, lam_4, lam_5, lam_6, hx_1, hx_2, hx_3, hx_4, hx_5, hx_6,
      hy_1, hy_2, hy_3, hy_4, hy_5, hy_6, mul_assoc, div_mul_div_comm, neg_mul_neg, e1, e3, e4]
    unfold E
    field_simp
    ring

end Moments

/-- **The heptagon fails OpenAI's `FieldCriterion`** for every transcendental `r > 2`. -/
theorem not_fieldCriterion (r : ℝ) (hr : 2 < r) (ht : Transcendental ℚ r) :
    ¬ FieldCriterion (heptagon r) := by
  rintro ⟨P, hP, hmul⟩
  obtain ⟨D, hD⟩ := GrahamSpherical.exists_real_derivation r 1 ht
  have h := weighted_trace (heptagon r) D lam P hP
  simp only [moment0 r hr, moment1 r D hr hD, moment1' r D hr hD, moment2 r D hr hD, zero_mul,
    zero_add] at h
  have hμ : μ (heptagon r) (P (some 1) (some 1)) = 1 := by
    rw [μ_eq_multiply, hmul 1 1, ite_eq_left rfl, IntermediateField.coe_one]
  rw [Finset.sum_eq_single (some 1)] at h
  · rw [Finset.sum_eq_single (some 1)] at h
    · rw [ite_eq_left ⟨rfl, rfl⟩, hμ, mul_one] at h
      exact E_ne_zero r hr h
    · intro β _ hβ
      rw [ite_eq_right (fun h => hβ h.2), zero_mul]
    · intro habs
      exact absurd (Finset.mem_univ _) habs
  · intro α _ hα
    exact Finset.sum_eq_zero fun β _ => by rw [ite_eq_right (fun h => hα h.1), zero_mul]
  · intro habs
    exact absurd (Finset.mem_univ _) habs

end

end HeptagonRamsey.Heptagon
