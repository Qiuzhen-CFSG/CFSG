module

public import Theory.Representation.SU3.CubicDegree.SchurOuter.AdjointBounds.OuterTranspose.Geometry.Coordinates
public import Theory.Representation.SU3.CubicDegree.SchurOuter.AdjointBounds.OuterTranspose.GeometryInterface
public import Theory.Representation.SL3.BinaryDefiningFactors.AdjointTensorTranspose

/-!
# From natural matrix coordinates to the literal adjoint graph operator

Conjugating trace-zero endomorphisms gives a linear change of coordinates.
Transpose intertwines conjugation by A with conjugation by its inverse
transpose. Scalar matrices act trivially, so projective covariance suffices,
and it remains valid after any embedding of the matrix field.

The resulting operator is the conjugate of literal transpose, on precisely
`AdjointSpace`. The construction uses neither an adjoint model for the binary
module nor irreducibility, a displacement estimate, or an offender bound.
Source: GM04, Proposition 4.11, internal pp.31--32.
-/

public noncomputable section
open Matrix BenderSuzuki.MatrixGroups
open Representation.SL3.BinaryDefiningFactors
namespace Representation.SU3.CubicDegree.SchurOuter.AdjointBounds.OuterTranspose.Geometry
variable {K : Type*} [Field K]

private theorem matrix_injective : Function.Injective (adjointMatrix (K := K)) := by
  intro X Y h
  apply Subtype.ext
  exact LinearMap.toMatrix'.injective (by simpa only [adjointMatrix_apply] using h)

private def coordinateChange (C : GL (Fin 3) K) : AdjointSpace K ≃ₗ[K] AdjointSpace K where
  toFun X := ⟨(C.val * LinearMap.toMatrix' X.val * (C⁻¹).val).toLin', by
    rw [LinearMap.mem_ker, Matrix.trace_toLin'_eq, Matrix.trace_units_conj]
    rw [← Matrix.trace_toLin'_eq, Matrix.toLin'_toMatrix']
    exact X.property⟩
  invFun X := ⟨((C⁻¹).val * LinearMap.toMatrix' X.val * C.val).toLin', by
    rw [LinearMap.mem_ker, Matrix.trace_toLin'_eq, Matrix.trace_units_conj']
    rw [← Matrix.trace_toLin'_eq, Matrix.toLin'_toMatrix']
    exact X.property⟩
  left_inv X := by
    apply Subtype.ext
    simp only [LinearMap.toMatrix'_toLin', mul_assoc, Units.inv_mul_cancel_left,
      Units.inv_mul, mul_one, Matrix.toLin'_toMatrix']
  right_inv X := by
    apply Subtype.ext
    simp only [LinearMap.toMatrix'_toLin', mul_assoc, Units.mul_inv_cancel_left,
      Units.mul_inv, mul_one, Matrix.toLin'_toMatrix']
  map_add' X Y := by
    apply Subtype.ext
    simp only [Submodule.coe_add, map_add, mul_add, add_mul]
  map_smul' c X := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, map_smul, Matrix.mul_smul, Matrix.smul_mul,
      RingHom.id_apply]

private theorem coordinateChange_matrix (C : GL (Fin 3) K) (X : AdjointSpace K) :
    adjointMatrix (coordinateChange C X) = C.val * adjointMatrix X * (C⁻¹).val := by
  simp only [adjointMatrix_apply]
  exact LinearMap.toMatrix'_toLin' _

private theorem coordinateChange_mul (A B : GL (Fin 3) K) (X : AdjointSpace K) :
    coordinateChange (A * B) X = coordinateChange A (coordinateChange B X) := by
  apply matrix_injective
  simp only [coordinateChange_matrix, _root_.mul_inv_rev, Units.val_mul, mul_assoc]

private theorem coordinateChange_scalar (c : Kˣ) (X : AdjointSpace K) :
    coordinateChange (GeneralLinearGroup.scalar (Fin 3) c) X = X := by
  apply matrix_injective
  rw [coordinateChange_matrix]
  change Matrix.scalar _ c.val * adjointMatrix X * Matrix.scalar _ (c⁻¹).val = _
  ext i j
  simp only [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  calc
    c.val * adjointMatrix X i j * (c⁻¹).val =
        (c.val * (c⁻¹).val) * adjointMatrix X i j := by ring
    _ = _ := by rw [Units.mul_inv, one_mul]

private theorem coordinateChange_projective_eq {A B : GL (Fin 3) K}
    (h : ProjGenLinGroup.mk A = ProjGenLinGroup.mk B) (X : AdjointSpace K) :
    coordinateChange A X = coordinateChange B X := by
  obtain ⟨c, rfl⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h
  rw [coordinateChange_mul, coordinateChange_scalar]

private def transposeEquiv : AdjointSpace K ≃ₗ[K] AdjointSpace K :=
  LinearEquiv.ofInvolutive (AdjointTensorTranspose.adjointTranspose K) (by
    intro X
    apply matrix_injective
    simp only [adjointMatrix_apply, AdjointTensorTranspose.matrix_adjointTranspose,
      Matrix.transpose_transpose])

private theorem transposeEquiv_matrix (X : AdjointSpace K) :
    adjointMatrix (transposeEquiv X) = (adjointMatrix X).transpose := by
  simp only [adjointMatrix_apply]
  exact AdjointTensorTranspose.matrix_adjointTranspose K X

private theorem transpose_coordinateChange (A : GL (Fin 3) K) (X : AdjointSpace K) :
    transposeEquiv (coordinateChange A X) =
      coordinateChange (inverseTranspose A) (transposeEquiv X) := by
  apply matrix_injective
  rw [transposeEquiv_matrix, coordinateChange_matrix, coordinateChange_matrix,
    transposeEquiv_matrix]
  change (A.val * adjointMatrix X * (A⁻¹).val).transpose =
    (A⁻¹).val.transpose * (adjointMatrix X).transpose * A.val.transpose
  simp only [Matrix.transpose_mul, mul_assoc]

variable {F : Type*} [Field F]

private theorem map_inverseTranspose (ι : F →+* K) (A : GL (Fin 3) F) :
    GeneralLinearGroup.map ι (inverseTranspose A) =
      inverseTranspose (GeneralLinearGroup.map ι A) := by
  apply Units.ext
  change (A⁻¹).val.transpose.map ι = ((GeneralLinearGroup.map ι A)⁻¹).val.transpose
  rw [← map_inv]
  rfl

private theorem map_projective_eq (ι : F →+* K) {A B : GL (Fin 3) F}
    (h : ProjGenLinGroup.mk A = ProjGenLinGroup.mk B) :
    ProjGenLinGroup.mk (GeneralLinearGroup.map ι A) =
      ProjGenLinGroup.mk (GeneralLinearGroup.map ι B) := by
  obtain ⟨c, rfl⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h
  simp only [map_mul, GeneralLinearGroup.map_scalar, ProjGenLinGroup.mk_scalar, mul_one]

private theorem coordinateChange_adjoint (J : HermitianForm 3 F) (ι : F →+* K)
    (g : J.specialSubgroup) (X : AdjointSpace K) :
    coordinateChange (GeneralLinearGroup.map ι g.val) X = adjoint J ι g X := by
  apply Subtype.ext
  rw [adjoint_apply]
  change Matrix.toLin' ((GeneralLinearGroup.map ι g.val).val *
    LinearMap.toMatrix' X.val * ((GeneralLinearGroup.map ι g.val)⁻¹).val) = _
  rw [← map_inv, Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
  rfl

private theorem coordinateChange_conjugate (C A : GL (Fin 3) K) (X : AdjointSpace K) :
    coordinateChange C (coordinateChange A X) =
      coordinateChange (C * A * C⁻¹) (coordinateChange C X) := by
  rw [← coordinateChange_mul, ← coordinateChange_mul]
  simp only [inv_mul_cancel_right]

variable {H : Type*} [Group H]

/-- Projective inverse-transpose coordinates construct a transpose-conjugate
operator intertwining every related pair of representatives on the actual
trace-zero adjoint space. -/
theorem adjointGraphIntertwiner_of_matrixCoordinates (J : HermitianForm 3 F)
    (ι : F →+* K) (p : J.specialSubgroup →* H) (α : MulAut H)
    (hc : HasMatrixTransposeCoordinates J p α) :
    AdjointGraphIntertwiner J ι p α := by
  obtain ⟨C, hC⟩ := hc
  let E := coordinateChange (GeneralLinearGroup.map ι C⁻¹)
  let S := E.trans (transposeEquiv.trans E.symm)
  have he (g : J.specialSubgroup) (X : AdjointSpace K) :
      E (adjoint J ι g X) =
        coordinateChange (GeneralLinearGroup.map ι (C⁻¹ * g.val * C)) (E X) := by
    dsimp only [E]
    rw [← coordinateChange_adjoint, coordinateChange_conjugate]
    simp only [map_mul, map_inv, inv_inv]
  refine ⟨S, ⟨E, ?_⟩, ?_⟩
  · intro X
    change adjointMatrix (E (E.symm (transposeEquiv (E X)))) = _
    rw [E.apply_symm_apply, transposeEquiv_matrix]
  · intro g h hgh
    apply LinearMap.ext
    intro X
    apply E.injective
    change E (E.symm (transposeEquiv (E (adjoint J ι g X)))) =
      E (adjoint J ι h (E.symm (transposeEquiv (E X))))
    rw [E.apply_symm_apply, he, he, E.apply_symm_apply, transpose_coordinateChange]
    have hh := map_projective_eq ι (hC g h hgh)
    rw [map_inverseTranspose] at hh
    exact coordinateChange_projective_eq hh.symm _

end Representation.SU3.CubicDegree.SchurOuter.AdjointBounds.OuterTranspose.Geometry
