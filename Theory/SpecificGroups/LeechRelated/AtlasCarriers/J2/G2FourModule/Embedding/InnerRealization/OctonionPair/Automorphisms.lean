module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.OctonionPair.Structure
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.OctonionPair.Products

/-!
# The two certified octonion automorphisms

The inverse certificates supply linear equivalences. The 64 basis-pair checks,
extended by bilinearity, prove preservation of the actual octonion product.
Thus the matrices define elements of the full split-octonion automorphism
model, with the indicated matrices for their inverses. Entrywise squaring
fixes the first and gives the inverse of the second.

Source and attribution: the preserved candidate in `../source/candidate.json`
and `../source/README.md`, for Aschbacher--Smith K.4.5 (printed p.460).
-/

@[expose] public section

namespace Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.OctonionPair
open Atlas.SplitOctonion

/-- All 64 basis products are preserved by the first matrix. -/
theorem aMatrix_basis_products : ∀ i j : Fin 8,
    aMatrix.mulVecLin (mul (basisVector i) (basisVector j)) =
      mul (aMatrix.mulVecLin (basisVector i)) (aMatrix.mulVecLin (basisVector j)) := by
  simp only [Matrix.mulVecLin_apply, basisVector, Matrix.mulVec_single_one]
  decide +kernel

/-- All 64 basis products are preserved by the second matrix. -/
theorem bMatrix_basis_products : ∀ i j : Fin 8,
    bMatrix.mulVecLin (mul (basisVector i) (basisVector j)) =
      mul (bMatrix.mulVecLin (basisVector i)) (bMatrix.mulVecLin (basisVector j)) := by
  simp only [Matrix.mulVecLin_apply, basisVector, Matrix.mulVec_single_one]
  decide +kernel

/-- The explicitly certified first octonion automorphism. -/
def a : Atlas.G2.Model Coeff :=
  ofMatrices aMatrix aMatrix MatrixCertificates.a_sq MatrixCertificates.a_sq aMatrix_basis_products

/-- The explicitly certified second octonion automorphism, with its displayed inverse. -/
def b : Atlas.G2.Model Coeff :=
  ofMatrices bMatrix bInvMatrix MatrixCertificates.b_inv_left MatrixCertificates.b_inv
    bMatrix_basis_products

@[simp] theorem matrixHom_a : matrixHom a = aMatrix :=
  matrixHom_ofMatrices _ _ _ _ _

@[simp] theorem matrixHom_b : matrixHom b = bMatrix :=
  matrixHom_ofMatrices _ _ _ _ _

@[simp] theorem matrixHom_a_inv : matrixHom a⁻¹ = aMatrix :=
  matrixHom_ofMatrices_inv _ _ _ _ _

@[simp] theorem matrixHom_b_inv : matrixHom b⁻¹ = bInvMatrix :=
  matrixHom_ofMatrices_inv _ _ _ _ _

theorem a_ne_one : a ≠ 1 := by
  intro h
  have hm : aMatrix = 1 := by
    simpa only [matrixHom_a, map_one] using congrArg matrixHom h
  exact (by decide +kernel : aMatrix ≠ 1) hm

theorem aMatrix_square_entry : ∀ i j, (aMatrix i j) ^ 2 = aMatrix i j := by
  unfold aMatrix
  decide +kernel

theorem bMatrix_square_entry : ∀ i j, (bMatrix i j) ^ 2 = bInvMatrix i j := by
  unfold bMatrix bInvMatrix
  decide +kernel

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.OctonionPair
