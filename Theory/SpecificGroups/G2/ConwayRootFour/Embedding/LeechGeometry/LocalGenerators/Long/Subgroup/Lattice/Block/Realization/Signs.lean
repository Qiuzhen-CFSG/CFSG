module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.Realization.Coordinates

/-!
# Faithfulness detects the two scalar signs

The rational expansion sends minus identity to minus identity. Its proved
injectivity therefore detects both signs exactly, before any lattice comparison.
This is used by the integral comparison to identify the literal Conway kernel.
Source matrix conventions are those of John Bray's ATLAS `6L34G1-Ar6aB0`.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Matrix Atlas.Algebra
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block.Realization

theorem rationalMatrices_injective : Function.Injective rationalMatrices := by
  intro g h he
  apply columnAction_injective
  apply Units.ext
  apply realification_injective
  exact congrArg Units.val he

theorem rationalMatrices_neg_one : rationalMatrices (-1) = -1 := by
  apply Units.ext
  change realification ((-1 : SixMatrix).conjTranspose) = -1
  rw [Matrix.conjTranspose_neg, Matrix.conjTranspose_one, map_neg, map_one]

theorem linearMatrices_neg_one : linearMatrices (-1) = LinearEquiv.neg ℚ := by
  ext x i
  simp [linearMatrices_apply, Matrix.neg_mulVec]

theorem linearAction_eq_neg_iff (g : matrixGroup) :
    linearAction g = LinearEquiv.neg ℚ ↔ g.val = -1 := by
  change linearMatrices (rationalMatrices g.val) = LinearEquiv.neg ℚ ↔ _
  rw [← linearMatrices_neg_one, linearMatrices.injective.eq_iff,
    ← rationalMatrices_neg_one, rationalMatrices_injective.eq_iff]

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block.Realization
