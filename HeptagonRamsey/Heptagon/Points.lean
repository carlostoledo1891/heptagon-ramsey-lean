import OAI.Combinatorics.EuclideanRamsey.Model
import OAI.Combinatorics.SphericalRamsey.RealDerivation

/-!
# Pálvölgyi's heptagon

The seven points `(0,0)` and `(j, ±√(j(2r−j)))`, `j ∈ {1, 3, 4}`, on the circle of centre `(r, 0)`
and radius `r`, with the weights `2, −2, −2, 2, 2, −1, −1` (arXiv:2609.23327, line 93), and a
derivation `D : Derivation ℤ ℝ ℝ` with `D r = 1`: `D (y_j) = j / y_j`.
-/

namespace HeptagonRamsey.Heptagon

open OAI OAI.EuclideanRamsey
open scoped BigOperators

noncomputable section

/-- The seven x-coordinates `0, 1, 1, 3, 3, 4, 4`, as naturals. -/
def hxN : Fin 7 → ℕ := ![0, 1, 1, 3, 3, 4, 4]

/-- The seven x-coordinates, as reals. -/
def hx (i : Fin 7) : ℝ := (hxN i : ℝ)

/-- The seven y-coordinates `0, ±√(2r−1), ±√(3(2r−3)), ±√(4(2r−4))`. -/
def hy (r : ℝ) : Fin 7 → ℝ :=
  ![0, Real.sqrt (2 * r - 1), -Real.sqrt (2 * r - 1),
    Real.sqrt (3 * (2 * r - 3)), -Real.sqrt (3 * (2 * r - 3)),
    Real.sqrt (4 * (2 * r - 4)), -Real.sqrt (4 * (2 * r - 4))]

/-- Pálvölgyi's heptagon. -/
def heptagon (r : ℝ) (i : Fin 7) : Space 2 := WithLp.toLp 2 ![hx i, hy r i]

/-- The weights `2, −2, −2, 2, 2, −1, −1`. -/
def lam : Fin 7 → ℝ := ![2, -2, -2, 2, 2, -1, -1]

@[simp] theorem heptagon_apply_zero (r : ℝ) (i : Fin 7) : heptagon r i 0 = hx i := rfl
@[simp] theorem heptagon_apply_one (r : ℝ) (i : Fin 7) : heptagon r i 1 = hy r i := rfl

@[simp] theorem hx_0 : hx 0 = 0 := by simp [hx, hxN]
@[simp] theorem hx_1 : hx 1 = 1 := by simp [hx, hxN]
@[simp] theorem hx_2 : hx 2 = 1 := by simp [hx, hxN]
@[simp] theorem hx_3 : hx 3 = 3 := by simp [hx, hxN]
@[simp] theorem hx_4 : hx 4 = 3 := by simp [hx, hxN]
@[simp] theorem hx_5 : hx 5 = 4 := by simp [hx, hxN]
@[simp] theorem hx_6 : hx 6 = 4 := by simp [hx, hxN]

@[simp] theorem hy_0 (r : ℝ) : hy r 0 = 0 := rfl
@[simp] theorem hy_1 (r : ℝ) : hy r 1 = Real.sqrt (2 * r - 1) := rfl
@[simp] theorem hy_2 (r : ℝ) : hy r 2 = -Real.sqrt (2 * r - 1) := rfl
@[simp] theorem hy_3 (r : ℝ) : hy r 3 = Real.sqrt (3 * (2 * r - 3)) := rfl
@[simp] theorem hy_4 (r : ℝ) : hy r 4 = -Real.sqrt (3 * (2 * r - 3)) := rfl
@[simp] theorem hy_5 (r : ℝ) : hy r 5 = Real.sqrt (4 * (2 * r - 4)) := rfl
@[simp] theorem hy_6 (r : ℝ) : hy r 6 = -Real.sqrt (4 * (2 * r - 4)) := rfl

@[simp] theorem lam_0 : lam 0 = 2 := rfl
@[simp] theorem lam_1 : lam 1 = -2 := rfl
@[simp] theorem lam_2 : lam 2 = -2 := rfl
@[simp] theorem lam_3 : lam 3 = 2 := rfl
@[simp] theorem lam_4 : lam 4 = 2 := rfl
@[simp] theorem lam_5 : lam 5 = -1 := rfl
@[simp] theorem lam_6 : lam 6 = -1 := rfl

/-- `y_i² = x_i (2r − x_i)`: the points lie on the circle of centre `(r, 0)` and radius `r`. -/
theorem hy_mul_self (r : ℝ) (hr : 2 < r) : ∀ i : Fin 7, hy r i * hy r i = hx i * (2 * r - hx i)
  | 0 => by simp
  | 1 => by rw [hy_1, hx_1, Real.mul_self_sqrt (by linarith)]; ring
  | 2 => by rw [hy_2, hx_2, neg_mul_neg, Real.mul_self_sqrt (by linarith)]; ring
  | 3 => by rw [hy_3, hx_3, Real.mul_self_sqrt (by linarith)]
  | 4 => by rw [hy_4, hx_4, neg_mul_neg, Real.mul_self_sqrt (by linarith)]
  | 5 => by rw [hy_5, hx_5, Real.mul_self_sqrt (by linarith)]
  | 6 => by rw [hy_6, hx_6, neg_mul_neg, Real.mul_self_sqrt (by linarith)]

theorem hy_ne_zero (r : ℝ) (hr : 2 < r) : ∀ i : Fin 7, i ≠ 0 → hy r i ≠ 0
  | 0, hi => absurd rfl hi
  | 1, _ => by rw [hy_1]; exact (Real.sqrt_pos.mpr (by linarith)).ne'
  | 2, _ => by rw [hy_2]; exact neg_ne_zero.mpr (Real.sqrt_pos.mpr (by linarith)).ne'
  | 3, _ => by rw [hy_3]; exact (Real.sqrt_pos.mpr (by linarith)).ne'
  | 4, _ => by rw [hy_4]; exact neg_ne_zero.mpr (Real.sqrt_pos.mpr (by linarith)).ne'
  | 5, _ => by rw [hy_5]; exact (Real.sqrt_pos.mpr (by linarith)).ne'
  | 6, _ => by rw [hy_6]; exact neg_ne_zero.mpr (Real.sqrt_pos.mpr (by linarith)).ne'

section Derivation

variable (D : Derivation ℤ ℝ ℝ)

theorem D_hx (i : Fin 7) : D (hx i) = 0 := D.map_natCast _

/-- `y_i · D(y_i) = x_i`, from `y_i² = x_i (2r − x_i)` and `D r = 1`. -/
theorem hy_mul_D_hy (r : ℝ) (hr : 2 < r) (hD : D r = 1) (i : Fin 7) :
    hy r i * D (hy r i) = hx i := by
  have htwo : D (2 : ℝ) = 0 := D.map_natCast 2
  have h := congrArg D (hy_mul_self r hr i)
  rw [Derivation.leibniz, Derivation.leibniz, map_sub, Derivation.leibniz, D_hx, hD, htwo] at h
  simp only [smul_eq_mul] at h
  linear_combination (1 / 2 : ℝ) * h

/-- `D(y_i) = x_i / y_i` for the six points off the origin. -/
theorem D_hy (r : ℝ) (hr : 2 < r) (hD : D r = 1) (i : Fin 7) (hi : i ≠ 0) :
    D (hy r i) = hx i / hy r i := by
  rw [eq_div_iff (hy_ne_zero r hr i hi), mul_comm]
  exact hy_mul_D_hy D r hr hD i

theorem D_hy_zero (r : ℝ) : D (hy r 0) = 0 := by simp

end Derivation

end

end HeptagonRamsey.Heptagon
