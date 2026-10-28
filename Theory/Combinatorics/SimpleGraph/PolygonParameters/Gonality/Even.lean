module
public import Theory.Combinatorics.SimpleGraph.PolygonParameters.DistanceMatrices
import all Theory.Combinatorics.SimpleGraph.PolygonParameters.DistanceMatrices

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Tactic.Module
public import Mathlib.Algebra.Polynomial.Monic

/-!
# Distance polynomials for even polygon gonality

The point distance matrices of a polygon of gonality `2*h` satisfy a
three-term recurrence. The last matrix has the exceptional coefficient
`t+1`. Evaluating the distance polynomials at point adjacency recovers these
matrices, so the terminal recurrence gives a monic annihilating polynomial
of degree `h+1`. Its two linear factors leave a shifted, scaled Chebyshev
polynomial.

This is the even spectral input to the finite-polygon argument cited in
Fong--Seitz I (1J), printed p.6, from Feit--Higman, J. Algebra 1 (1964),
114--131, DOI 10.1016/0021-8693(64)90028-6. The identities are derived from
`Datum`; they do not assert the allowed-gonality conclusion. The internal
import of `DistanceMatrices` permits the entrywise recurrence proof without
changing that module's public boundary.
-/

public noncomputable section
namespace SimpleGraph.PolygonParameters.Datum
open scoped BigOperators
variable {V : Type*} {G : SimpleGraph V} [Fintype V] {h s t : ℕ}
attribute [local instance] Classical.propDecidable
local instance gonalityEvenDecidableEq0 : DecidableEq V := Classical.decEq _

/-- The complete interior recurrence, including both exceptional endpoints. -/
theorem even_recurrence (D : Datum G (2*h) s t) (hh : 2 ≤ h)
    (k : ℕ) (hk : 0 < k) (hkh : k < h) :
    D.distanceMatrix 1 * D.distanceMatrix k =
      (if k=1 then (s : ℝ)*(t+1) else (s : ℝ)*t) • D.distanceMatrix (k-1) +
      ((s : ℝ)-1) • D.distanceMatrix k +
      (if k+1=h then (t : ℝ)+1 else 1) • D.distanceMatrix (k+1) := by
  ext u v
  rw [D.matrix_mul_apply (by omega) (by exact ⟨h, by omega⟩)]
  obtain ⟨d,hd⟩ := D.even_point_distance u.property v.property
  have hb := D.diameter u.val v.val
  have hdb : d ≤ h := by omega
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, distanceMatrix]
  split_ifs <;> try omega
  all_goals ring

/-- At the diameter all the neighboring lines lead back towards the base. -/
theorem even_last_recurrence (D : Datum G (2*h) s t) (hh : 2 ≤ h) :
    D.distanceMatrix 1 * D.distanceMatrix h =
      ((s : ℝ)*t) • D.distanceMatrix (h-1) +
      (((s : ℝ)-1)*(t+1)) • D.distanceMatrix h := by
  ext u v
  rw [D.matrix_mul_apply (by omega) (by exact ⟨h, by omega⟩)]
  obtain ⟨d,hd⟩ := D.even_point_distance u.property v.property
  have hb := D.diameter u.val v.val
  have hdb : d ≤ h := by omega
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, distanceMatrix]
  split_ifs <;> try omega
  all_goals ring
end SimpleGraph.PolygonParameters.Datum

namespace SimpleGraph.PolygonParameters.Gonality
open Polynomial
/-- Distance polynomials, with the first intersection number distinguished. -/
def distancePolynomial (s t : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | k+2 => (X-C (s-1))*distancePolynomial s t (k+1) -
      C (if k=0 then s*(t+1) else s*t)*distancePolynomial s t k

/-- The terminal recurrence polynomial for an even polygon of gonality `2*h`. -/
def evenAnnihilator (h : ℕ) (s t : ℝ) : ℝ[X] :=
  (X-C ((s-1)*(t+1)))*distancePolynomial s t h -
    C (s*t*(t+1))*distancePolynomial s t (h-1)
end SimpleGraph.PolygonParameters.Gonality

namespace SimpleGraph.PolygonParameters.Datum
open Polynomial Gonality
variable {V : Type*} {G : SimpleGraph V} [Fintype V] {h s t : ℕ}
attribute [local instance] Classical.propDecidable
local instance gonalityEvenDecidableEq1 : DecidableEq V := Classical.decEq _

theorem even_distancePolynomial_aeval (D : Datum G (2*h) s t) (hh : 2 ≤ h)
    (k : ℕ) (hk : k ≤ h) :
    aeval (D.distanceMatrix 1) (distancePolynomial s t k) =
      (if k=h then (t:ℝ)+1 else 1) • D.distanceMatrix k := by
  induction k using Nat.twoStepInduction with
  | zero => simp [distancePolynomial, show 0≠h by omega, D.distanceMatrix_zero]
  | one => simp [distancePolynomial, show 1≠h by omega]
  | more k ih₀ ih₁ =>
    have h₀ := ih₀ (by omega)
    have h₁ := ih₁ (by omega)
    simp only [show k≠h by omega, show k+1≠h by omega, ite_false, one_smul] at h₀ h₁
    have hr := D.even_recurrence hh (k+1) (by omega) (by omega)
    simp only [Nat.add_sub_cancel, Nat.add_eq_right] at hr
    simp only [distancePolynomial, map_sub, map_mul, aeval_X, aeval_C,
      Algebra.algebraMap_eq_smul_one, h₀, h₁, sub_mul, smul_mul_assoc, one_mul]
    linear_combination (norm := module) hr

theorem evenAnnihilator_aeval (D : Datum G (2*h) s t) (hh : 2 ≤ h) :
    aeval (D.distanceMatrix 1) (evenAnnihilator h s t) = 0 := by
  have h₀ := D.even_distancePolynomial_aeval hh h le_rfl
  have h₁ := D.even_distancePolynomial_aeval hh (h-1) (by omega)
  simp only [ite_true] at h₀
  simp only [show h-1≠h by omega, ite_false, one_smul] at h₁
  simp only [evenAnnihilator, map_sub, map_mul, aeval_X, aeval_C,
    Algebra.algebraMap_eq_smul_one, h₀, h₁, sub_mul, smul_mul_assoc,
    mul_smul_comm, one_mul, smul_smul, D.even_last_recurrence hh, smul_add]
  module
end SimpleGraph.PolygonParameters.Datum

namespace SimpleGraph.PolygonParameters.Gonality
open Polynomial

/-- The shifted, scaled Chebyshev recurrence used by the even spectrum. -/
def spectralPolynomial (s t : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X-C (s-1)
  | k+2 => (X-C (s-1))*spectralPolynomial s t (k+1) -
      C (s*t)*spectralPolynomial s t k

private theorem evenAnnihilator_recurrence (s t : ℝ) (k : ℕ) (hk : 2 ≤ k) :
    evenAnnihilator (k+2) s t =
      (X-C (s-1))*evenAnnihilator (k+1) s t - C (s*t)*evenAnnihilator k s t := by
  have hrec (i : ℕ) (hi : 0 < i) : distancePolynomial s t (i+2) =
      (X-C (s-1))*distancePolynomial s t (i+1) - C (s*t)*distancePolynomial s t i := by
    rw [distancePolynomial, if_neg (by omega)]
  have he : k-1+2=k+1 := by omega
  have he' : k-1+1=k := by omega
  have hrec' := hrec (k-1) (by omega)
  rw [he, he'] at hrec'
  simp only [evenAnnihilator, Nat.add_sub_cancel, show k+2-1=k+1 by omega]
  rw [hrec k (by omega), hrec']
  ring

/-- The two trivial eigenvalues split off, leaving the Chebyshev factor. -/
theorem evenAnnihilator_factorization (s t : ℝ) (h : ℕ) (hh : 2 ≤ h) :
    evenAnnihilator h s t =
      (X-C (s*(t+1)))*(X+C (t+1))*spectralPolynomial s t (h-1) := by
  obtain ⟨k,rfl⟩ : ∃ k, h=k+2 := ⟨h-2, by omega⟩
  clear hh
  induction k using Nat.twoStepInduction with
  | zero => norm_num [evenAnnihilator, distancePolynomial, spectralPolynomial, map_sub, map_add, map_mul]; ring
  | one => norm_num [evenAnnihilator, distancePolynomial, spectralPolynomial, map_sub, map_add, map_mul]; ring
  | more k ih₀ ih₁ =>
    rw [evenAnnihilator_recurrence s t (k+2) (by omega)]
    rw [show k+2+1=k+1+2 by omega, ih₁, ih₀]
    have he : k+1+2-1=k+1+1 := by omega
    have he' : k+2-1=k+1 := by omega
    have he'' : k+2+2-1=k+1+2 := by omega
    rw [he,he',he'']
    conv_rhs => rw [spectralPolynomial]
    ring
end SimpleGraph.PolygonParameters.Gonality

namespace SimpleGraph.PolygonParameters.Gonality
open Polynomial

private theorem spectralPolynomial_monic_natDegree (s t : ℝ) (k : ℕ) :
    (spectralPolynomial s t k).Monic ∧ (spectralPolynomial s t k).natDegree = k := by
  induction k using Nat.twoStepInduction with
  | zero => simp [spectralPolynomial]
  | one => exact ⟨monic_X_sub_C _, natDegree_X_sub_C _⟩
  | more k ih₀ ih₁ =>
    rw [spectralPolynomial]
    have hm := (monic_X_sub_C (s-1)).mul ih₁.1
    have hd : ((X-C (s-1))*spectralPolynomial s t (k+1)).natDegree=k+2 := by
      rw [(monic_X_sub_C (s-1)).natDegree_mul ih₁.1, natDegree_X_sub_C, ih₁.2]
      omega
    have hlt : (C (s*t)*spectralPolynomial s t k).natDegree <
        ((X-C (s-1))*spectralPolynomial s t (k+1)).natDegree := by
      have hb := natDegree_C_mul_le (s*t) (spectralPolynomial s t k)
      rw [hd, ih₀.2] at *
      omega
    exact ⟨hm.sub_of_left (degree_lt_degree hlt),
      (natDegree_sub_eq_left_of_natDegree_lt hlt).trans hd⟩

theorem spectralPolynomial_monic (s t : ℝ) (k : ℕ) :
    (spectralPolynomial s t k).Monic := (spectralPolynomial_monic_natDegree s t k).1

theorem spectralPolynomial_natDegree (s t : ℝ) (k : ℕ) :
    (spectralPolynomial s t k).natDegree = k := (spectralPolynomial_monic_natDegree s t k).2

theorem evenAnnihilator_monic (s t : ℝ) (h : ℕ) (hh : 2 ≤ h) :
    (evenAnnihilator h s t).Monic := by
  rw [evenAnnihilator_factorization s t h hh]
  exact ((monic_X_sub_C _).mul (monic_X_add_C _)).mul (spectralPolynomial_monic s t _)

theorem evenAnnihilator_natDegree (s t : ℝ) (h : ℕ) (hh : 2 ≤ h) :
    (evenAnnihilator h s t).natDegree = h+1 := by
  rw [evenAnnihilator_factorization s t h hh,
    ((monic_X_sub_C _).mul (monic_X_add_C _)).natDegree_mul (spectralPolynomial_monic s t _),
    (monic_X_sub_C _).natDegree_mul (monic_X_add_C _),
    natDegree_X_sub_C, natDegree_X_add_C, spectralPolynomial_natDegree]
  omega
end SimpleGraph.PolygonParameters.Gonality
