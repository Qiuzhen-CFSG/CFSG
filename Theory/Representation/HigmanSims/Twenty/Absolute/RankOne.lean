module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.RingTheory.Adjoin.Basic

/-!
# Matrix density from a rank-one operator and two orbit bases

Suppose a matrix algebra contains the rank-one operators obtained from
all columns of an invertible matrix and all rows of another invertible
matrix. The supplied one-sided inverses express coordinate rank-one
operators as linear combinations. A unit pairing then gives every matrix
unit by multiplication. This is the algebraic step of the HS twenty-space
certificate in `Twenty/source/density.json`.
-/

public section
open Matrix

namespace Sporadic.LeechRelated.HS.Twenty.Absolute

theorem eq_top_of_rankOne
    {F : Type*} [CommSemiring F] {n : Type*} [Fintype n] [DecidableEq n]
    (A : Subalgebra F (Matrix n n F)) (C Cinv R Rinv : Matrix n n F)
    (u r : n → F) (hC : C * Cinv = 1) (hR : Rinv * R = 1)
    (hpair : dotProduct r u = 1)
    (hc : ∀ k, vecMulVec (fun x => C x k) r ∈ A)
    (hr : ∀ k, vecMulVec u (R k) ∈ A) : A = ⊤ := by
  have hcol (i : n) : vecMulVec (Pi.single i 1) r ∈ A := by
    have he : vecMulVec (Pi.single i 1) r =
        ∑ k, Cinv k i • vecMulVec (fun x => C x k) r := by
      ext x y
      simp only [vecMulVec_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
      trans (∑ k, C x k * Cinv k i) * r y
      · rw [← Matrix.mul_apply, hC]
        simp [Matrix.one_apply, Pi.single_apply, eq_comm]
      · simp only [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _
        ac_rfl
    rw [he]
    exact A.sum_mem fun k _ => A.smul_mem (hc k) _
  have hrow (j : n) : vecMulVec u (Pi.single j 1) ∈ A := by
    have he : vecMulVec u (Pi.single j 1) =
        ∑ k, Rinv j k • vecMulVec u (R k) := by
      ext x y
      simp only [vecMulVec_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
      trans u x * (∑ k, Rinv j k * R k y)
      · rw [← Matrix.mul_apply, hR]
        simp [Matrix.one_apply, Pi.single_apply, eq_comm]
      · simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ac_rfl
    rw [he]
    exact A.sum_mem fun k _ => A.smul_mem (hr k) _
  have units (i j : n) : Matrix.single i j (1 : F) ∈ A := by
    have he : vecMulVec (Pi.single i 1) r * vecMulVec u (Pi.single j 1) =
        Matrix.single i j 1 := by
      rw [Matrix.vecMulVec_mul_vecMulVec, hpair, one_smul]
      ext x y
      by_cases hi : i = x <;> by_cases hj : j = y <;>
        simp [vecMulVec_apply, hi, hj, eq_comm]
    rw [← he]
    exact A.mul_mem (hcol i) (hrow j)
  apply top_unique
  intro M _
  rw [show M = ∑ i, ∑ j, M i j • Matrix.single i j 1 by
    simpa using Matrix.matrix_eq_sum_single M]
  exact A.sum_mem fun i _ => A.sum_mem fun j _ => A.smul_mem (units i j) _

end Sporadic.LeechRelated.HS.Twenty.Absolute
