module
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Centers of central quotients of GL₂

Over a field in which two is nonzero, an element of GL₂ whose image in a
quotient by a central subgroup is central must itself be central. The normality
instance is supplied by the caller and is retained throughout the quotient
construction. No finiteness hypothesis is needed, so the result includes F₃.

Quotient centrality makes the conjugate of every elementary transvection a
scalar multiple of that transvection. Conjugation preserves trace, and every
such transvection has trace two. Cancelling this nonzero trace forces the
scalar to be one. Mathlib's recognition of scalar matrices by commutation with
all transvections then identifies the original element as central.

This supplies the center-lifting step behind the scalar-image description in
Brauer, *On finite Desarguesian planes. II*, §2, p125, (2.1)--(2.4), used in
the odd-central-kernel cardinality argument. Unlike a general assertion that
centers lift through central quotients, the proof uses the GL₂ matrix structure.
-/

namespace Matrix.GeneralLinearGroup

public theorem mem_center_of_quotient_mem_center
    {F : Type*} [Field F] (htwo : (2 : F) ≠ 0)
    (Z : Subgroup (GL (Fin 2) F)) [Z.Normal]
    (hZ : Z ≤ Subgroup.center (GL (Fin 2) F)) (A : GL (Fin 2) F)
    (hA : QuotientGroup.mk' Z A ∈ Subgroup.center (GL (Fin 2) F ⧸ Z)) :
    A ∈ Subgroup.center (GL (Fin 2) F) := by
  apply mem_center_iff_val_mem_range_scalar.mpr
  apply Matrix.mem_range_scalar_of_commute_transvectionStruct
  intro trans
  let elementary : GL (Fin 2) F :=
    ⟨trans.toMatrix, trans.inv.toMatrix, trans.mul_inv, trans.inv_mul⟩
  have hquot : QuotientGroup.mk' Z (A * elementary * A⁻¹) =
      QuotientGroup.mk' Z elementary := by
    rw [map_mul, map_mul, map_inv,
      ← Subgroup.mem_center_iff.mp hA (QuotientGroup.mk' Z elementary)]
    simp [mul_assoc]
  obtain ⟨kernel, hkernel, heq⟩ := (QuotientGroup.mk'_eq_mk' Z).mp hquot.symm
  obtain ⟨coeff, hcoeff⟩ := mem_center_iff_val_mem_range_scalar.mp (hZ hkernel)
  have hmatrix : A.val * trans.toMatrix * (A⁻¹).val =
      trans.toMatrix * Matrix.scalar (Fin 2) coeff := by
    simpa only [Units.val_mul, hcoeff] using (congrArg Units.val heq).symm
  have htrace : Matrix.trace trans.toMatrix = 2 := by
    simp [Matrix.TransvectionStruct.toMatrix, Matrix.transvection,
      Matrix.trace_add, trans.hij]
  have hcoeff_one : coeff = 1 := by
    have htr := congrArg Matrix.trace hmatrix
    rw [Matrix.trace_units_conj] at htr
    have hscalar_trace : Matrix.trace (trans.toMatrix * Matrix.scalar (Fin 2) coeff) =
        Matrix.trace trans.toMatrix * coeff := by
      simp only [Matrix.scalar_apply, Matrix.trace, Matrix.diag,
        Matrix.mul_diagonal, Finset.sum_mul]
    rw [hscalar_trace, htrace] at htr
    exact (mul_right_cancel₀ htwo (by simpa [mul_comm] using htr.symm) : coeff = 1)
  have hcomm : A * elementary * A⁻¹ = elementary := by
    apply Units.ext
    simpa [hcoeff_one] using hmatrix
  have hcomm' : A * elementary = elementary * A := by
    exact (mul_inv_eq_iff_eq_mul).mp hcomm
  exact (congrArg Units.val hcomm').symm

end Matrix.GeneralLinearGroup
