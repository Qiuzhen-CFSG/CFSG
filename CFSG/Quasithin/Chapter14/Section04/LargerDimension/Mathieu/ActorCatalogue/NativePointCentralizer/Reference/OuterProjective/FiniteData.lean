module
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.LinearNormalizer.CoreRecognition.ProjectiveAction
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.Matrix.ToLin
/-!
# Outer-generator certificates for the endpoint action

The displayed permutations act on endpoints by inverse right multiplication
by the original ATLAS generators C and D. The target tables verify all 231
published representatives and their endpoint labels. Both generators satisfy
J M = M (1 + J), so a structural binary-row argument transports the entire
scalar triple from the checked image of its representative.

Every finite identity is checked by the Lean kernel. No matrix-group
enumeration is used. See `source/README.md` for reproduction and attribution.
These certificates discharge the generator premises of the outer action in
`Reference.OuterProjective`, used for H.12.1(5,9) and 14.4.12 of
Aschbacher--Smith (printed pp.393--394 and 1011--1012).
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Native
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open CoreProjectiveAction
namespace ReferenceOuterAction
/-- Endpoint permutation for inverse right multiplication by C. -/
def permC : Equiv.Perm (Fin 22) where
  toFun := ![0, 7, 15, 9, 21, 13, 16, 1, 8, 3, 10, 11, 12, 5, 14, 2, 6, 20, 18, 19, 17, 4]
  invFun := ![0, 7, 15, 9, 21, 13, 16, 1, 8, 3, 10, 11, 12, 5, 14, 2, 6, 20, 18, 19, 17, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def targetC : Fin 231 → Fin 231 :=
  ![0, 5, 6, 12, 18, 1, 2, 7, 8, 14, 13, 15, 3, 10, 9, 11, 16, 17, 4, 19, 20, 47, 84, 23, 67, 88, 91, 79, 28, 85, 30, 92, 93, 80, 82, 81, 36, 86, 94, 83, 87, 89, 90, 152, 151, 60, 155, 21, 48, 156, 143, 51, 150, 53, 131, 76, 153, 154, 74, 105, 45, 61, 62, 191, 70, 193, 66, 24, 133, 192, 64, 194, 195, 149, 58, 139, 55, 196, 124, 27, 33, 35, 34, 39, 22, 29, 37, 40, 25, 41, 42, 26, 31, 32, 38, 95, 96, 107, 108, 100, 99, 109, 110, 103, 104, 59, 111, 97, 98, 101, 102, 106, 161, 113, 166, 165, 116, 170, 157, 162, 163, 121, 167, 142, 78, 158, 164, 168, 148, 160, 159, 54, 169, 68, 202, 201, 205, 137, 197, 75, 200, 203, 123, 50, 198, 199, 204, 206, 128, 73, 52, 44, 43, 56, 57, 46, 49, 118, 125, 130, 129, 112, 119, 120, 126, 115, 114, 122, 127, 132, 117, 171, 175, 173, 178, 172, 176, 179, 174, 177, 180, 211, 207, 208, 212, 210, 213, 214, 215, 209, 216, 63, 69, 65, 71, 72, 77, 138, 144, 145, 140, 135, 134, 141, 146, 136, 147, 182, 183, 189, 185, 181, 184, 186, 187, 188, 190, 217, 218, 221, 222, 219, 220, 223, 224, 226, 225, 230, 228, 229, 227]

private theorem twistC : matrixJ * matrixC = matrixC * (1 + matrixJ) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem generatorC_rows : ∀ i : Fin 231,
    Matrix.vecMul (projectiveVector i) matrixC ∈
      scalarLine (projectiveVector (targetC i)) := by
  simp only [scalarLine, Set.mem_insert_iff, Set.mem_singleton_iff]
  decide +kernel

/-- Endpoint permutation for inverse right multiplication by D. -/
def permD : Equiv.Perm (Fin 22) where
  toFun := ![17, 0, 3, 12, 14, 20, 7, 9, 16, 13, 1, 2, 11, 6, 8, 19, 4, 10, 21, 15, 5, 18]
  invFun := ![1, 10, 11, 2, 16, 20, 13, 6, 14, 7, 17, 12, 3, 9, 4, 19, 8, 0, 21, 15, 5, 18]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def targetD : Fin 231 → Fin 231 :=
  ![3, 1, 4, 2, 0, 21, 24, 22, 26, 12, 25, 23, 47, 43, 45, 48, 46, 44, 62, 61, 60, 116, 113, 114, 115, 112, 117, 59, 135, 67, 134, 136, 33, 28, 80, 82, 79, 81, 83, 96, 97, 98, 95, 154, 35, 188, 111, 141, 230, 198, 224, 228, 202, 216, 190, 155, 89, 151, 187, 27, 205, 225, 213, 41, 203, 161, 201, 29, 170, 199, 223, 182, 107, 165, 229, 167, 227, 207, 180, 110, 179, 153, 17, 177, 214, 191, 219, 126, 159, 56, 176, 156, 215, 217, 163, 194, 193, 218, 146, 173, 184, 210, 132, 166, 186, 226, 157, 72, 181, 200, 129, 127, 138, 143, 140, 139, 142, 137, 118, 119, 121, 123, 120, 122, 99, 101, 102, 16, 100, 36, 86, 84, 87, 85, 30, 32, 31, 8, 10, 6, 11, 9, 5, 7, 65, 64, 63, 66, 51, 49, 50, 58, 124, 196, 206, 91, 55, 78, 178, 90, 133, 189, 42, 54, 39, 74, 76, 105, 131, 18, 68, 147, 145, 152, 38, 125, 88, 174, 209, 183, 106, 108, 69, 34, 208, 158, 77, 57, 192, 144, 94, 160, 14, 164, 162, 130, 37, 20, 220, 71, 109, 171, 93, 172, 40, 197, 13, 104, 128, 185, 175, 148, 15, 169, 168, 53, 92, 52, 204, 195, 149, 19, 150, 70, 222, 221, 75, 103, 211, 73, 212]

private theorem twistD : matrixJ * matrixD = matrixD * (1 + matrixJ) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem generatorD_rows : ∀ i : Fin 231,
    Matrix.vecMul (projectiveVector i) matrixD ∈
      scalarLine (projectiveVector (targetD i)) := by
  simp only [scalarLine, Set.mem_insert_iff, Set.mem_singleton_iff]
  decide +kernel

private theorem row_cancel_left (v w : Row) : v + (v + w) = w := by
  funext i
  exact CharTwo.add_cancel_left _ _

private theorem image_triple (f : Row →ₗ[ZMod 2] Row) (v w r : Row)
    (h : f w = f v + r) :
    f '' {v, w, v + w} = {f v, r, f v + r} := by
  rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton,
    map_add, h, row_cancel_left, Set.pair_comm (f v + r) r]

private theorem vecMul_twist (v : Row) (M J : Matrix12)
    (h : J * M = M * (1 + J)) :
    Matrix.vecMul (Matrix.vecMul v J) M =
      Matrix.vecMul v M + Matrix.vecMul (Matrix.vecMul v M) J := by
  rw [Matrix.vecMul_vecMul, h, ← Matrix.vecMul_vecMul, Matrix.vecMul_add,
    Matrix.vecMul_one]

private theorem triple_image_twisted (v : Row) (M J : Matrix12)
    (h : J * M = M * (1 + J)) :
    (fun w => Matrix.vecMul w M) ''
        {v, Matrix.vecMul v J, v + Matrix.vecMul v J} =
      {Matrix.vecMul v M, Matrix.vecMul (Matrix.vecMul v M) J,
        Matrix.vecMul v M + Matrix.vecMul (Matrix.vecMul v M) J} :=
  image_triple (Matrix.vecMulLinear M) v (Matrix.vecMul v J)
    (Matrix.vecMul (Matrix.vecMul v M) J) (vecMul_twist v M J h)

private theorem scalarLine_image_twisted (v : Row) (M : Matrix12)
    (h : matrixJ * M = M * (1 + matrixJ)) :
    (fun w => Matrix.vecMul w M) '' scalarLine v = scalarLine (Matrix.vecMul v M) :=
  triple_image_twisted v M matrixJ h

private theorem generatorC_endpoints : ∀ i : Fin 231,
    endpointPair (targetC i) = (endpointPair i).image permC.symm := by
  decide +kernel

/-- Compatibility of the original outer matrix generator C. -/
theorem compatible_C : Compatible unitC permC := by
  intro i
  have he : targetC i = pairAction permC⁻¹ i :=
    endpointPair_injective ((generatorC_endpoints i).trans (pairAction_spec permC⁻¹ i).symm)
  change (fun w => Matrix.vecMul w matrixC) '' _ = _
  rw [scalarLine_image_twisted _ _ twistC, scalarLine_of_mem (generatorC_rows i), he]

private theorem generatorD_endpoints : ∀ i : Fin 231,
    endpointPair (targetD i) = (endpointPair i).image permD.symm := by
  decide +kernel

/-- Compatibility of the original outer matrix generator D. -/
theorem compatible_D : Compatible unitD permD := by
  intro i
  have he : targetD i = pairAction permD⁻¹ i :=
    endpointPair_injective ((generatorD_endpoints i).trans (pairAction_spec permD⁻¹ i).symm)
  change (fun w => Matrix.vecMul w matrixD) '' _ = _
  rw [scalarLine_image_twisted _ _ twistD, scalarLine_of_mem (generatorD_rows i), he]

end ReferenceOuterAction
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Native
