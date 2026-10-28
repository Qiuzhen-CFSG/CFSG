module

public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution.Certificate.Filtration.Blocks

/-!
# A certified three-layer basis for the M₁₁ quotient candidates

The explicit matrix P is invertible with the supplied inverse Q. For both
marked generators, AₛP = PTₛ; each Tₛ is upper block triangular with three
100-dimensional blocks. Each diagonal block consists of ten consecutive copies
of the actual eleven-point augmentation action in the basis eᵢ + e₁₀.

`adaptedCoordinates` gives the change of basis as a linear equivalence;
`diagonalCopy_augmentation` and `diagonalCopy_point` connect its factors to the
actual representations. The parent norm-ideal certificate can transport this
flag once its independent surjective-lift certificate is proved. No group representation or
ideal-membership property of the candidate 300-dimensional matrices is assumed
or asserted here.

The witnesses and their provenance are in `source/README.md`.
Source application: Aschbacher–Smith G.7.3(2), printed p.348/PDF p.359, citing
James, J. Algebra 27 (1973), 57–111.
-/

@[expose] public section

open Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution
namespace Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution.CertificateFiltration

/-- The supplied Q is a left inverse to the supplied P. -/
theorem inverse_mul_basis : inverseMatrix * basisMatrix = 1 :=
  Packed.matrix_mul_one inverseColumns basisColumns inverseColumns_length
    (fun j => (all_columns j).1)

/-- The same explicit Q is also a right inverse. -/
theorem basis_mul_inverse : basisMatrix * inverseMatrix = 1 :=
  (mul_eq_one_comm (a := inverseMatrix) (b := basisMatrix)).mp inverse_mul_basis

theorem generator_intertwines (s : Fin 2) :
    CertificateData.actionMatrix s * basisMatrix = basisMatrix * transformedMatrix s := by
  rw [← originalMatrix_eq]
  exact Packed.matrix_mul_eq (originalColumns s) basisColumns basisColumns (transformedColumns s)
    (originalColumns_length s) basisColumns_length (fun j => (all_columns j).2.1 s)

theorem generator_conjugation (s : Fin 2) :
    inverseMatrix * CertificateData.actionMatrix s * basisMatrix = transformedMatrix s := by
  rw [Matrix.mul_assoc, generator_intertwines, ← Matrix.mul_assoc, inverse_mul_basis, one_mul]

/-- Adapted coordinates to the original candidate quotient coordinates. -/
noncomputable def adaptedCoordinates : CertificateData.Space ≃ₗ[ZMod 2] CertificateData.Space :=
  LinearEquiv.ofLinearMap basisMatrix.mulVecLin inverseMatrix.mulVecLin
    (by rw [← Matrix.mulVecLin_mul, basis_mul_inverse, Matrix.mulVecLin_one])
    (by rw [← Matrix.mulVecLin_mul, inverse_mul_basis, Matrix.mulVecLin_one])

theorem adaptedCoordinates_intertwines (s : Fin 2) (v : CertificateData.Space) :
    CertificateData.action s (adaptedCoordinates v) = adaptedCoordinates ((transformedMatrix s).mulVec v) := by
  change (CertificateData.actionMatrix s).mulVec (basisMatrix.mulVec v) =
    basisMatrix.mulVec ((transformedMatrix s).mulVec v)
  rw [Matrix.mulVec_mulVec, generator_intertwines, ← Matrix.mulVec_mulVec]
/-- One of the ten consecutive augmentation copies in one of the three layers. -/
def diagonalCopy (s : Fin 2) (layer : Fin 3) (copy : Fin 10) :
    Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  fun r j => transformedMatrix s (coordinate layer copy r) (coordinate layer copy j)

theorem diagonalCopy_eq (s : Fin 2) (layer : Fin 3) (copy : Fin 10) :
    diagonalCopy s layer copy = augmentationMatrix (CertificateData.generator s) := by
  ext r j
  simpa only [diagonalCopy, ↓reduceIte] using diagonal_blocks s layer copy copy r j

/-- Actual augmentation-module interpretation of every diagonal copy. -/
theorem diagonalCopy_augmentation (s : Fin 2) (layer : Fin 3) (copy : Fin 10)
    (v : Fin 10 → ZMod 2) :
    augmentationCoordinates ((diagonalCopy s layer copy).mulVec v) =
      augmentationRepresentation (CertificateData.generator s) (augmentationCoordinates v) := by
  rw [diagonalCopy_eq]
  exact augmentationCoordinates_equivariant _ _

/-- The same diagonal factor in the parent consumer's literal point module. -/
theorem diagonalCopy_point (s : Fin 2) (layer : Fin 3) (copy : Fin 10)
    (v : Fin 10 → ZMod 2) :
    pointCoordinates ((diagonalCopy s layer copy).mulVec v) =
      pointRepresentation (CertificateData.generator s) (pointCoordinates v) := by
  rw [diagonalCopy_eq]
  exact pointCoordinates_equivariant _ _

end Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution.CertificateFiltration
