module

public import Theory.SpecificGroups.SL2.Affine.Structure
public import Theory.SpecificGroups.PSL3.LinearThreeLocalCores

/-!
# Structural facts for the actual PSL₃ point and line local groups

The published point- and line-local equivalences identify the projective
matrix subgroups with the natural special affine group. Applying the affine
structure theorems proves their perfectness and their intrinsic identities
F*(L) = O₂(L), without assuming that either local group is a block.

These discharge the perfectness and generalized Fitting inputs in the
L₃(q) branch of Aschbacher–Smith F.1.12(I)(1),(II), printed pp.262–264.
The remaining block and solvable-residual assembly is separate.
-/

public section
namespace Matrix.PSL3.LinearThree
variable (F : Type*) [Field F] [Finite F]

/-- Perfectness of the projective point-local group, through its actual affine coordinates. -/
theorem pointLocal_isPerfect (hcard : 4 ≤ Nat.card F) :
    Group.IsPerfect (pointLocal F) :=
  Matrix.SL2.isPerfect_of_equiv_affine F hcard (pointLocalEquivAffine F)

/-- Perfectness of the projective line-local group, through its actual affine coordinates. -/
theorem lineLocal_isPerfect (hcard : 4 ≤ Nat.card F) :
    Group.IsPerfect (lineLocal F) :=
  Matrix.SL2.isPerfect_of_equiv_affine F hcard (lineLocalEquivAffine F)

/-- The point-local group has generalized Fitting subgroup equal to its own two-core. -/
theorem pointLocal_generalizedFitting_eq_twoCore [CharP F 2] :
    Theory.GroupTheory.generalizedFitting (pointLocal F) = pCore 2 (pointLocal F) :=
  Matrix.SL2.generalizedFitting_eq_twoCore_of_equiv_affine F (pointLocalEquivAffine F)

/-- The line-local group has generalized Fitting subgroup equal to its own two-core. -/
theorem lineLocal_generalizedFitting_eq_twoCore [CharP F 2] :
    Theory.GroupTheory.generalizedFitting (lineLocal F) = pCore 2 (lineLocal F) :=
  Matrix.SL2.generalizedFitting_eq_twoCore_of_equiv_affine F (lineLocalEquivAffine F)

end Matrix.PSL3.LinearThree
