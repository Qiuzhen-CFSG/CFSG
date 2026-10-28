module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.SuzukiProjection.MatrixIdentification.Representation.Kernel.AmbientRelations.Data
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Scalar and coordinate transport for the full binary F₄ matrices

Scalar extension from `ZMod 2` to the actual binary coefficient field and a
bijection of all 52 basis coordinates define a ring homomorphism of matrix
algebras. The comparison with the four ambient root elements is a separate
obligation. This construction transports a full matrix, including all Cartan
and root coordinates.

Source context: the integral Geck model of the middle-node Levi used in
Aschbacher–Smith F.1.12(I)(5), printed pp.263–264 of `refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section
namespace ReeF4.Parabolics.BinarySuzuki.MatrixIdentification.KernelProof.AmbientComputation
open Theory.AlgebraicGroup

/-- Extend scalars and relabel all 52 coordinates of the tabulated matrices. -/
def fullMatrixMap (e : Fin 52 ≃ F4Chevalley.BasisIndex) :
    Matrix (Fin 52) (Fin 52) (ZMod 2) →+*
      Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex (CoefficientField 0) :=
  (Matrix.reindexRingEquiv (CoefficientField 0) e).toRingHom.comp
    (ZMod.castHom (dvd_refl 2) (CoefficientField 0)).mapMatrix

/-- The comparison at a pair of corresponding basis coordinates is entrywise. -/
theorem fullMatrixMap_apply (e : Fin 52 ≃ F4Chevalley.BasisIndex)
    (M : Matrix (Fin 52) (Fin 52) (ZMod 2)) (i j : Fin 52) :
    fullMatrixMap e M (e i) (e j) =
      ZMod.castHom (dvd_refl 2) (CoefficientField 0) (M i j) := by
  simp [fullMatrixMap, Matrix.reindex_apply]

end ReeF4.Parabolics.BinarySuzuki.MatrixIdentification.KernelProof.AmbientComputation
