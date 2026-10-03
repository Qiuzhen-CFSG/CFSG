module
public import ABG.Basic

/-!
# Norm one for determinants of the standard GU2 group

An element of the actual `GU2 p n hn` has determinant whose order divides
`p^n + 1`. This is the opening determinant assertion of ABG Chapter II,
Section 2, article page 17 (`page-018.tex`), used to bound the determinant
levels and construct the later unitary scalar decomposition.

Take determinants in the defining Hermitian isometry equation. The Gram
matrix is the identity, and the determinant of conjugate transpose is the
q-Frobenius image of the determinant. Thus `d^q * d = 1`, giving the stated
power and order conditions. The original GaloisField, Hermitian involution,
and GU2 subgroup inclusion are used throughout; no identification with SL2
or group-order recognition is assumed.
-/

namespace ABG

public theorem GU2_det_pow_eq_one
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) (A : GU2 p n hn) :
    Matrix.GeneralLinearGroup.det A.val ^ (p ^ n + 1) = 1 := by
  apply Units.ext
  change ((A.val : Matrix (Fin 2) (Fin 2) (GaloisField p (2 * n))).det) ^ (p ^ n + 1) = 1
  have hA := (unitaryForm 2 p n hn).mem_unitarySubgroup_iff A.val |>.mp A.property
  have hd := congrArg Matrix.det hA
  have hconj :
      ((unitaryForm 2 p n hn).conjTranspose
        (A.val : Matrix (Fin 2) (Fin 2) (GaloisField p (2 * n)))).det =
      ((unitaryForm 2 p n hn).conj
        ((A.val : Matrix (Fin 2) (Fin 2) (GaloisField p (2 * n))).det)) := by
    change (((unitaryForm 2 p n hn).conj.mapMatrix
      (A.val : Matrix (Fin 2) (Fin 2) (GaloisField p (2 * n))).transpose)).det = _
    rw [← RingEquiv.map_det, Matrix.det_transpose]
  simp only [Matrix.det_mul, hconj] at hd
  change ((unitaryForm 2 p n hn).conj
    ((A.val : Matrix (Fin 2) (Fin 2) (GaloisField p (2 * n))).det)) *
    Matrix.det (1 : Matrix (Fin 2) (Fin 2) (GaloisField p (2 * n))) *
    ((A.val : Matrix (Fin 2) (Fin 2) (GaloisField p (2 * n))).det) = Matrix.det 1 at hd
  simpa only [unitaryForm, iterateFrobeniusEquiv_def, Matrix.det_one, mul_one,
    pow_succ] using hd

public theorem GU2_det_orderOf_dvd
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) (A : GU2 p n hn) :
    orderOf (Matrix.GeneralLinearGroup.det A.val) ∣ p ^ n + 1 :=
  orderOf_dvd_iff_pow_eq_one.mpr (GU2_det_pow_eq_one p n hn A)

end ABG
