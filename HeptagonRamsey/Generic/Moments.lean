module

public import OAI.Combinatorics.EuclideanRamsey.NineGeometry
public import Mathlib.LinearAlgebra.Lagrange

@[expose] public section

/-!
# The finite identities of Theorem A.3 (arXiv:2609.23327v1, .tex 395–434)

Seven distinct reals `t_i`, the points `p(t_i) = ((1−t_i²)/(1+t_i²), 2t_i/(1+t_i²))` (OpenAI's
`NineGeometry.circlePoint`), `H = ∏ (X − t_i)`, `H'(t_i) = ∏_{j≠i} (t_i − t_j)`, `g = (X − t₁)(X − t₂)(X − t₃)`,
`λ_i = (1+t_i²)²/H'(t_i)`, and a derivation with `D(t_i) = g(t_i)` at all seven nodes. Everything is one Mathlib
lemma, `Lagrange.coeff_eq_sum`: `Σ_i P(t_i)/H'(t_i) = P.coeff 6` for `deg P ≤ 6` (the paper's (A.2)).

- `Σλ = 0`, `Σλ p = 0`, `Σλ p pᵀ = 0` (each coordinate polynomial has degree ≤ 4);
- `Σλ D(p) = 0` (degrees 4 and 5);
- `M = Σλ D(p) pᵀ` symmetric: `λ (D(x) y − D(y) x) = −2 g (1+t²)/H'`, degree 5. `M` is NOT zero in general (H1's
  finding: Equation (2) of the main text is stronger than what A.3 provides; Lemma A.1 needs only symmetry);
- `E = Σλ ‖D(p)‖² = 4 Σ g²/H' = 4` (`g²` is monic of degree 6).
-/

namespace HeptagonRamsey.Generic

open OAI OAI.EuclideanRamsey Polynomial
open scoped BigOperators

noncomputable section

/-- The paper's seven points `p(t_i)`, through OpenAI's stereographic `circlePoint`. -/
def circ (t : Fin 7 → ℝ) (i : Fin 7) : Space 2 := NineGeometry.circlePoint (t i)

@[simp] theorem circ_zero (t : Fin 7 → ℝ) (i : Fin 7) :
    circ t i 0 = (1 - t i ^ 2) / (1 + t i ^ 2) := NineGeometry.circlePoint_zero (t i)

@[simp] theorem circ_one (t : Fin 7 → ℝ) (i : Fin 7) :
    circ t i 1 = 2 * t i / (1 + t i ^ 2) := NineGeometry.circlePoint_one (t i)

variable (t : Fin 7 → ℝ)

/-- `H'(t_i) = ∏_{j ≠ i} (t_i − t_j)`. -/
def Hd (i : Fin 7) : ℝ := ∏ j ∈ Finset.univ.erase i, (t i - t j)

/-- `Hd` is the derivative of `H = ∏ (X − t_i)` at the node (Mathlib's `nodalWeight`). -/
theorem Hd_eq_derivative (i : Fin 7) :
    Hd t i = (derivative (Lagrange.nodal Finset.univ t)).eval (t i) := by
  have h := Lagrange.nodalWeight_eq_eval_derivative_nodal (s := Finset.univ) (v := t)
    (Finset.mem_univ i)
  rw [Lagrange.nodalWeight, Finset.prod_inv_distrib] at h
  exact inv_inj.mp h

/-- The paper's weights `λ_i = (1+t_i²)²/H'(t_i)`. -/
def weight (i : Fin 7) : ℝ := (1 + t i ^ 2) ^ 2 / Hd t i

/-- `g(u) = (u − t₁)(u − t₂)(u − t₃)`. -/
def g (u : ℝ) : ℝ := (u - t 0) * (u - t 1) * (u - t 2)

/-- `g` as a polynomial. -/
def G : ℝ[X] := (X - C (t 0)) * (X - C (t 1)) * (X - C (t 2))

@[simp] theorem eval_G (u : ℝ) : (G t).eval u = g t u := by simp [G, g]

theorem G_monic : (G t).Monic :=
  ((monic_X_sub_C _).mul (monic_X_sub_C _)).mul (monic_X_sub_C _)

theorem G_natDegree : (G t).natDegree = 3 := by
  rw [G, ((monic_X_sub_C _).mul (monic_X_sub_C _)).natDegree_mul (monic_X_sub_C _),
    (monic_X_sub_C _).natDegree_mul (monic_X_sub_C _), natDegree_X_sub_C, natDegree_X_sub_C,
    natDegree_X_sub_C]

theorem g_zero : g t (t 0) = 0 := by simp [g]
theorem g_one : g t (t 1) = 0 := by simp [g]
theorem g_two : g t (t 2) = 0 := by simp [g]

variable {t}

theorem Hd_ne_zero (ht : Function.Injective t) (i : Fin 7) : Hd t i ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hj =>
    sub_ne_zero.mpr fun h => (Finset.ne_of_mem_erase hj) (ht h).symm

/-- **Lagrange**: `Σ_i P(t_i)/H'(t_i) = P.coeff 6` when `deg P ≤ 6`. -/
theorem interp (ht : Function.Injective t) (P : ℝ[X]) (hP : P.natDegree ≤ 6) :
    ∑ i, P.eval (t i) / Hd t i = P.coeff 6 := by
  have h := Lagrange.coeff_eq_sum (s := (Finset.univ : Finset (Fin 7))) (v := t)
    (fun x _ y _ hxy => ht hxy) (P := P) (by
      rw [Finset.card_univ, Fintype.card_fin]
      exact (Polynomial.degree_le_of_natDegree_le hP).trans_lt
        (by exact_mod_cast (show (6 : ℕ) < 7 by norm_num)))
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact h.symm

theorem interp_eq (ht : Function.Injective t) (P : ℝ[X]) (hP : P.natDegree ≤ 6) (f : Fin 7 → ℝ)
    (hf : ∀ i, f i = P.eval (t i) / Hd t i) : ∑ i, f i = P.coeff 6 := by
  rw [Finset.sum_congr rfl fun i _ => hf i, interp ht P hP]

theorem interp_zero (ht : Function.Injective t) (P : ℝ[X]) (hP : P.natDegree ≤ 5) (f : Fin 7 → ℝ)
    (hf : ∀ i, f i = P.eval (t i) / Hd t i) : ∑ i, f i = 0 := by
  rw [interp_eq ht P (hP.trans (by norm_num)) f hf]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

/-- The paper's (A.2): `Σ t_i^k / H'(t_i) = 0` for `0 ≤ k ≤ 5`. -/
theorem interp_pow (ht : Function.Injective t) (k : ℕ) (hk : k ≤ 5) :
    ∑ i, t i ^ k / Hd t i = 0 :=
  interp_zero ht (X ^ k) (by rw [natDegree_X_pow]; exact hk) _ fun i => by simp

/-- The paper's (A.2): `Σ t_i^6 / H'(t_i) = 1`. -/
theorem interp_pow_six (ht : Function.Injective t) : ∑ i, t i ^ 6 / Hd t i = 1 := by
  rw [interp_eq ht (X ^ 6) (by rw [natDegree_X_pow]) _ fun i => by simp]
  simp

theorem one_add_sq_ne_zero (u : ℝ) : (1 + u ^ 2 : ℝ) ≠ 0 := by positivity

section Ordinary

variable (ht : Function.Injective t)
include ht

/-- `Σλ = 0`. -/
theorem moment_one : ∑ i, weight t i = 0 :=
  interp_zero ht ((1 + X ^ 2) ^ 2) (by compute_degree!) _ fun i => by simp [weight]

/-- `Σλ p = 0`. -/
theorem moment_lin : ∀ j : Fin 2, ∑ i, weight t i * circ t i j = 0
  | 0 => interp_zero ht ((1 - X ^ 2) * (1 + X ^ 2)) (by compute_degree!) _ fun i => by
      have := one_add_sq_ne_zero (t i)
      have := Hd_ne_zero ht i
      simp only [weight, circ_zero, eval_mul, eval_add, eval_sub, eval_one, eval_pow, eval_X]
      field_simp
  | 1 => interp_zero ht (C 2 * X * (1 + X ^ 2)) (by compute_degree!) _ fun i => by
      have := one_add_sq_ne_zero (t i)
      have := Hd_ne_zero ht i
      simp only [weight, circ_one, eval_mul, eval_add, eval_C, eval_one, eval_pow, eval_X]
      field_simp

/-- `Σλ p pᵀ = 0`. -/
theorem moment_quad : ∀ j k : Fin 2, ∑ i, weight t i * circ t i j * circ t i k = 0
  | 0, 0 => interp_zero ht ((1 - X ^ 2) ^ 2) (by compute_degree!) _ fun i => by
      have := one_add_sq_ne_zero (t i)
      have := Hd_ne_zero ht i
      simp only [weight, circ_zero, eval_sub, eval_one, eval_pow, eval_X]
      field_simp
  | 0, 1 => interp_zero ht (C 2 * X * (1 - X ^ 2)) (by compute_degree!) _ fun i => by
      have := one_add_sq_ne_zero (t i)
      have := Hd_ne_zero ht i
      simp only [weight, circ_zero, circ_one, eval_mul, eval_sub, eval_C, eval_one, eval_pow,
        eval_X]
      field_simp
  | 1, 0 => interp_zero ht (C 2 * X * (1 - X ^ 2)) (by compute_degree!) _ fun i => by
      have := one_add_sq_ne_zero (t i)
      have := Hd_ne_zero ht i
      simp only [weight, circ_zero, circ_one, eval_mul, eval_sub, eval_C, eval_one, eval_pow,
        eval_X]
      field_simp
  | 1, 1 => interp_zero ht (C 4 * X ^ 2) (by compute_degree!) _ fun i => by
      have := one_add_sq_ne_zero (t i)
      have := Hd_ne_zero ht i
      simp only [weight, circ_one, eval_mul, eval_C, eval_pow, eval_X]
      field_simp
      ring

/-- The paper's form of the energy: `Σλ_i b_i² = 4` with `b_i = 2 g(t_i)/(1+t_i²)`. -/
theorem energy_b : ∑ i, weight t i * (2 * g t (t i) / (1 + t i ^ 2)) ^ 2 = 4 := by
  rw [interp_eq ht (C 4 * (G t * G t)) (by unfold G; compute_degree!) _ fun i => ?_]
  · rw [coeff_C_mul]
    have hm := (G_monic t).mul (G_monic t)
    have hn : (G t * G t).natDegree = 6 := by
      rw [(G_monic t).natDegree_mul (G_monic t), G_natDegree]
    rw [← hn, hm.coeff_natDegree, mul_one]
  · have := one_add_sq_ne_zero (t i)
    have := Hd_ne_zero ht i
    simp only [weight, eval_mul, eval_C, eval_G]
    field_simp
    ring

end Ordinary

section Derivative

variable (D : Derivation ℤ ℝ ℝ)

theorem D_sq (u : ℝ) : D (u ^ 2) = 2 * u * D u := by
  rw [sq, Derivation.leibniz]; simp only [smul_eq_mul]; ring

theorem D_two : D (2 : ℝ) = 0 := D.map_natCast 2

/-- `D x = −4 u D(u)/(1+u²)²` for `x = (1−u²)/(1+u²)`. -/
theorem D_param_x (u : ℝ) : D ((1 - u ^ 2) / (1 + u ^ 2)) = -4 * u * D u / (1 + u ^ 2) ^ 2 := by
  have h1 : (1 + u ^ 2 : ℝ) ≠ 0 := by positivity
  rw [Derivation.leibniz_div, map_sub, map_add, D_sq, Derivation.map_one_eq_zero]
  simp only [smul_eq_mul]
  field_simp
  ring

/-- `D y = 2 (1−u²) D(u)/(1+u²)²` for `y = 2u/(1+u²)`. -/
theorem D_param_y (u : ℝ) : D (2 * u / (1 + u ^ 2)) = 2 * (1 - u ^ 2) * D u / (1 + u ^ 2) ^ 2 := by
  have h1 : (1 + u ^ 2 : ℝ) ≠ 0 := by positivity
  rw [Derivation.leibniz_div, map_add, D_sq, Derivation.map_one_eq_zero, Derivation.leibniz,
    D_two]
  simp only [smul_eq_mul]
  field_simp
  ring

variable (hD : ∀ i, D (t i) = g t (t i))
include hD

theorem D_circ_zero (i : Fin 7) :
    D (circ t i 0) = -4 * t i * g t (t i) / (1 + t i ^ 2) ^ 2 := by
  rw [circ_zero, D_param_x, hD]

theorem D_circ_one (i : Fin 7) :
    D (circ t i 1) = 2 * (1 - t i ^ 2) * g t (t i) / (1 + t i ^ 2) ^ 2 := by
  rw [circ_one, D_param_y, hD]

/-- The paper's `D(p_i) = b_i J p_i` with `b_i = 2 g(t_i)/(1+t_i²)` and `J(x, y) = (−y, x)`. -/
theorem D_circ_eq_bJ (i : Fin 7) :
    D (circ t i 0) = -(2 * g t (t i) / (1 + t i ^ 2)) * circ t i 1 ∧
      D (circ t i 1) = (2 * g t (t i) / (1 + t i ^ 2)) * circ t i 0 := by
  have h1 : (1 + t i ^ 2 : ℝ) ≠ 0 := by positivity
  refine ⟨?_, ?_⟩
  · rw [D_circ_zero D hD, circ_one]; field_simp; ring
  · rw [D_circ_one D hD, circ_zero]; field_simp

variable (ht : Function.Injective t)
include ht

/-- `Σλ D(p) = 0`. -/
theorem moment_D : ∀ j : Fin 2, ∑ i, weight t i * D (circ t i j) = 0
  | 0 => interp_zero ht (C (-4) * X * G t) (by unfold G; compute_degree!) _ fun i => by
      have := one_add_sq_ne_zero (t i)
      have := Hd_ne_zero ht i
      rw [D_circ_zero D hD]
      simp only [weight, eval_mul, eval_C, eval_X, eval_G]
      field_simp
  | 1 => interp_zero ht (C 2 * (1 - X ^ 2) * G t) (by unfold G; compute_degree!) _ fun i => by
      have := one_add_sq_ne_zero (t i)
      have := Hd_ne_zero ht i
      rw [D_circ_one D hD]
      simp only [weight, eval_mul, eval_C, eval_sub, eval_one, eval_pow, eval_X, eval_G]
      field_simp

/-- `M = Σλ D(p) pᵀ` is symmetric: `M₀₁ − M₁₀ = −2 Σ g (1+t²)/H' = 0`. -/
theorem moment_M01 :
    ∑ i, weight t i * D (circ t i 0) * circ t i 1 = ∑ i, weight t i * D (circ t i 1) * circ t i 0 := by
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  refine interp_zero ht (C (-2) * (1 + X ^ 2) * G t) (by unfold G; compute_degree!) _ fun i => ?_
  have := one_add_sq_ne_zero (t i)
  have := Hd_ne_zero ht i
  rw [D_circ_zero D hD, D_circ_one D hD]
  simp only [weight, circ_zero, circ_one, eval_mul, eval_C, eval_add, eval_one, eval_pow, eval_X,
    eval_G]
  field_simp
  ring

theorem moment_M : ∀ j k : Fin 2,
    ∑ i, weight t i * D (circ t i j) * circ t i k = ∑ i, weight t i * D (circ t i k) * circ t i j
  | 0, 0 => rfl
  | 0, 1 => moment_M01 D hD ht
  | 1, 0 => (moment_M01 D hD ht).symm
  | 1, 1 => rfl

/-- `E = Σλ ‖D(p)‖² = 4 Σ g²/H' = 4`. -/
theorem energy : ∑ j : Fin 2, ∑ i, weight t i * D (circ t i j) * D (circ t i j) = 4 := by
  rw [Fin.sum_univ_two, ← Finset.sum_add_distrib]
  have hdeg : (C 4 * (G t * G t)).natDegree ≤ 6 := by unfold G; compute_degree!
  rw [interp_eq ht (C 4 * (G t * G t)) hdeg _ fun i => ?_]
  · rw [coeff_C_mul]
    have hm := (G_monic t).mul (G_monic t)
    have hn : (G t * G t).natDegree = 6 := by
      rw [(G_monic t).natDegree_mul (G_monic t), G_natDegree]
    rw [← hn, hm.coeff_natDegree, mul_one]
  · have := one_add_sq_ne_zero (t i)
    have := Hd_ne_zero ht i
    rw [D_circ_zero D hD, D_circ_one D hD]
    simp only [weight, eval_mul, eval_C, eval_G]
    field_simp
    ring

end Derivative

end

end HeptagonRamsey.Generic
