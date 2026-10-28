module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.Realization.IcosianComparison.Core
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.Realization.ScalarInterface

/-!
# Compatibility with right rational quaternions

Each four-by-four block of the displayed comparison is left quaternion
multiplication. The left/right commutation identity therefore gives compatibility
with every right rational quaternion, retaining both golden coefficient blocks.
This checks the literal `rightScalar` and `icosianRightMul` conventions used
by the marked comparison, rather than an abstract scalar-group identification.
The coordinate data are the attributed ATLAS data from `ComparisonData`.

-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Atlas.Algebra Atlas.Lattices Atlas.Codes
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block.Realization
namespace IcosianComparison

private def leftQuaternion (a b c d : ℚ) : Matrix (Fin 4) (Fin 4) ℚ :=
  !![a,-b,-c,-d;b,a,-d,c;c,d,a,-b;d,-c,b,a]

private theorem leftQuaternion_commute (a b c d e f g h : ℚ) :
    Commute (leftQuaternion a b c d) (rightQuaternion e f g h) := by
  change leftQuaternion a b c d * rightQuaternion e f g h =
    rightQuaternion e f g h * leftQuaternion a b c d
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leftQuaternion, rightQuaternion, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

private def block (i : Fin 3) (t : Fin 2) (j : Fin 6) : Matrix (Fin 4) (Fin 4) ℚ :=
  leftQuaternion (comparisonCandidateMatrix (i,0,t) (j,0))
    (comparisonCandidateMatrix (i,1,t) (j,0))
    (comparisonCandidateMatrix (i,2,t) (j,0))
    (comparisonCandidateMatrix (i,3,t) (j,0))

private theorem block_apply : ∀ i t j k l,
    block i t j k l = comparisonCandidateMatrix (i,k,t) (j,l) := by decide +kernel

private def targetRight (a b c d : ℚ) : Matrix IcosianRealIndex IcosianRealIndex ℚ :=
  fun i j => if i.1=j.1 ∧ i.2.2=j.2.2 then rightQuaternion a b c d i.2.1 j.2.1 else 0

private theorem matrix_right (a b c d : ℚ) :
    comparisonCandidateMatrix * rightScalar a b c d =
      targetRight a b c d * comparisonCandidateMatrix := by
  ext ⟨i,k,t⟩ ⟨j,l⟩
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℚ => M k l)
    (leftQuaternion_commute
      (comparisonCandidateMatrix (i,0,t) (j,0))
      (comparisonCandidateMatrix (i,1,t) (j,0))
      (comparisonCandidateMatrix (i,2,t) (j,0))
      (comparisonCandidateMatrix (i,3,t) (j,0)) a b c d).eq
  change (block i t j * rightQuaternion a b c d) k l =
    (rightQuaternion a b c d * block i t j) k l at h
  simpa [Matrix.mul_apply, Fintype.sum_prod_type, rightScalar, targetRight,
    ite_and, ite_mul, mul_ite, block_apply] using h

private theorem realCoordinates_right (z : IcosianRationalCoordinates) (a b c d : ℚ) :
    icosianRealCoordinates (icosianRightMul z (scalarQuaternion a b c d)) =
      targetRight a b c d *ᵥ icosianRealCoordinates z := by
  ext ⟨i,k,t⟩
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  simp [targetRight, ite_and, ite_mul]
  fin_cases k <;> fin_cases t <;>
    simp [icosianRealCoordinates, icosianQuaternionCoordinate, icosianRightMul,
      scalarQuaternion, rightQuaternion, Fin.sum_univ_succ,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;> ring

end IcosianComparison

/-- The explicit comparison intertwines every rational right quaternion. -/
theorem quaternionComparison_right (a b c d : ℚ) (x : Space) :
    quaternionComparison (rightScalar a b c d *ᵥ x) =
      icosianRightMul (quaternionComparison x) (scalarQuaternion a b c d) := by
  apply icosianRealCoordinates.injective
  rw [quaternionComparison_coordinates, IcosianComparison.realCoordinates_right,
    quaternionComparison_coordinates, Matrix.mulVec_mulVec, IcosianComparison.matrix_right,
    ← Matrix.mulVec_mulVec]

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block.Realization
