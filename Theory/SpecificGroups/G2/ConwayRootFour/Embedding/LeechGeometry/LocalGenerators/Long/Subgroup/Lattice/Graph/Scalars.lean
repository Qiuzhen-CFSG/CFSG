module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Graph.Isometry

/-!
# Marked scalar compatibility of the graph swap

Every four-by-four block is left quaternion multiplication, so it commutes
with rational right scalars. The actual icosian comparison and published A₄
marking transport this to the literal scalarFive and leechCentralProjection.
Source: Aschbacher, Sporadic Groups (1994), 49.5, p.283. The numerical
certificates and their ATLAS provenance are recorded in `Graph.Data`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Atlas.Algebra Atlas.Lattices Atlas.Conway Atlas.LinearAlgebra
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Graph
open Block Block.Realization

private def leftQuaternion (a b c d : ℚ) : Matrix (Fin 4) (Fin 4) ℚ :=
  !![a,-b,-c,-d;b,a,-d,c;c,d,a,-b;d,-c,b,a]

private theorem leftQuaternion_commute (a b c d e f g h : ℚ) :
    Commute (leftQuaternion a b c d) (rightQuaternion e f g h) := by
  change leftQuaternion a b c d * rightQuaternion e f g h =
    rightQuaternion e f g h * leftQuaternion a b c d
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leftQuaternion, rightQuaternion, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

private def quaternionBlock (i j : Fin 6) : Matrix (Fin 4) (Fin 4) ℚ :=
  leftQuaternion (swapMatrix (i,0) (j,0)) (swapMatrix (i,1) (j,0))
    (swapMatrix (i,2) (j,0)) (swapMatrix (i,3) (j,0))

private theorem quaternionBlock_apply : ∀ i j k l,
    quaternionBlock i j k l = swapMatrix (i,k) (j,l) := by decide +kernel

theorem swapMatrix_right (a b c d : ℚ) :
    Commute swapMatrix (rightScalar a b c d) := by
  change swapMatrix * rightScalar a b c d = rightScalar a b c d * swapMatrix
  ext ⟨i,k⟩ ⟨j,l⟩
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℚ => M k l)
    (leftQuaternion_commute (swapMatrix (i,0) (j,0)) (swapMatrix (i,1) (j,0))
      (swapMatrix (i,2) (j,0)) (swapMatrix (i,3) (j,0)) a b c d).eq
  change (quaternionBlock i j * rightQuaternion a b c d) k l =
    (rightQuaternion a b c d * quaternionBlock i j) k l at h
  simpa [Matrix.mul_apply, Fintype.sum_prod_type, rightScalar,
    ite_mul, mul_ite, quaternionBlock_apply] using h

theorem swapLinear_right (a b c d : ℚ) (x : Space) :
    swapLinear (rightScalar a b c d *ᵥ x) = rightScalar a b c d *ᵥ swapLinear x := by
  change swapMatrix *ᵥ (rightScalar a b c d *ᵥ x) =
    rightScalar a b c d *ᵥ (swapMatrix *ᵥ x)
  rw [Matrix.mulVec_mulVec, (swapMatrix_right a b c d).eq, ← Matrix.mulVec_mulVec]

private theorem scalar_extension_intertwines (u : rationalScalarUnits) (x : Space) :
    (fullIsometryEquiv (icosianScalarsToCo0 u.val)).val (matrixComparison x) =
      matrixComparison (scalarMatrix u *ᵥ x) := by
  rw [icosianScalarsToCo0_extension]
  change icosianComparison (icosianScalarRepresentation u.val
    (icosianComparison.symm (icosianComparison (quaternionComparison x)))) = _
  rw [icosianComparison.symm_apply_apply,
    scalar_intertwines quaternionComparison quaternionComparison_right]
  rfl

/-- The integral swap commutes with every literal rational norm-one scalar. -/
theorem swap_scalar (u : rationalScalarUnits) :
    Commute swap (icosianScalarsToCo0 u.val) := by
  apply fullIsometryEquiv.injective
  rw [map_mul, map_mul]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  obtain ⟨x,rfl⟩ := matrixComparison.surjective z
  change (fullIsometryEquiv swap).val
      ((fullIsometryEquiv (icosianScalarsToCo0 u.val)).val (matrixComparison x)) =
    (fullIsometryEquiv (icosianScalarsToCo0 u.val)).val
      ((fullIsometryEquiv swap).val (matrixComparison x))
  rw [scalar_extension_intertwines, swap_intertwines, swap_intertwines,
    scalar_extension_intertwines]
  congr 1
  exact swapLinear_right _ _ _ _ _

/-- The literal scalar A₄ marking required by `LatticeGraph`. -/
theorem swap_commute (a : alternatingGroup fourPoints) :
    Commute (scalarFive (latticeBlock.marking a)) (leechCentralProjection swap) := by
  have ha : matrixMarking a ∈ rationalScalarToFive.range :=
    matrixMarking_range ▸ (show matrixMarking a ∈ matrixMarking.range from ⟨a,rfl⟩)
  obtain ⟨u,hu⟩ := ha
  rw [latticeBlock_marking, ← hu, rationalScalarToFive_projection]
  exact (swap_scalar u).symm.map leechCentralProjection

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Graph
