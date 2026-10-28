module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.Realization.Coordinates

/-!
# Right quaternion scalars commute with the block action

The explicit right multiplication matrices commute with left Eisenstein
multiplication. Matrix expansion and the inverse-adjoint action extend this
to every element of the literal generated group. The rational coordinates
remain accessible to the marked lattice-comparison and graph-normalizer proofs.
Source matrix conventions: John Bray, ATLAS `6L34G1-Ar6aB0`.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Matrix Atlas.Algebra
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block.Realization

/-- Right multiplication by a rational Hamilton quaternion (a,b,c,d). -/
def rightQuaternion (a b c d : ℚ) : Matrix (Fin 4) (Fin 4) ℚ :=
  !![a,-b,-c,-d;b,a,d,-c;c,-d,a,b;d,c,-b,a]

theorem omegaMatrix_commute_rightQuaternion (a b c d : ℚ) :
    Commute omegaMatrix (rightQuaternion a b c d) := by
  change omegaMatrix * rightQuaternion a b c d = rightQuaternion a b c d * omegaMatrix
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [omegaMatrix, rightQuaternion, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem scalarRealification_commute_rightQuaternion (z : Eisenstein) (a b c d : ℚ) :
    Commute (scalarRealification z) (rightQuaternion a b c d) := by
  change scalarRealification z * rightQuaternion a b c d = rightQuaternion a b c d * scalarRealification z
  rw [scalarRealification_apply, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one,
    Matrix.smul_mul, Matrix.mul_smul, (omegaMatrix_commute_rightQuaternion a b c d).eq]

/-- The same right quaternion acts on each of the six coordinates. -/
def rightScalar (a b c d : ℚ) : RealMatrix := fun i j =>
  if i.1 = j.1 then rightQuaternion a b c d i.2 j.2 else 0

theorem realification_commute_rightScalar (A : SixMatrix) (a b c d : ℚ) :
    Commute (realification A) (rightScalar a b c d) := by
  change realification A * rightScalar a b c d = rightScalar a b c d * realification A
  ext ⟨i,k⟩ ⟨j,l⟩
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℚ => M k l)
    (scalarRealification_commute_rightQuaternion (A i j) a b c d).eq
  simpa [realification, rightScalar, Matrix.mul_apply, Fintype.sum_prod_type] using h

/-- Every literal matrix-group element commutes with all rational right quaternions. -/
theorem rationalAction_commute_rightScalar (g : matrixGroup) (a b c d : ℚ) :
    Commute (rationalAction g).val (rightScalar a b c d) :=
  realification_commute_rightScalar _ a b c d

theorem linearAction_rightScalar (g : matrixGroup) (a b c d : ℚ) (x : Space) :
    linearAction g (rightScalar a b c d *ᵥ x) =
      rightScalar a b c d *ᵥ linearAction g x := by
  change (rationalAction g).val *ᵥ (rightScalar a b c d *ᵥ x) =
    rightScalar a b c d *ᵥ ((rationalAction g).val *ᵥ x)
  rw [Matrix.mulVec_mulVec, (rationalAction_commute_rightScalar g a b c d).eq,
    ← Matrix.mulVec_mulVec]

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block.Realization
