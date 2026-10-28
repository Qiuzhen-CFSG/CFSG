module

public import Theory.SpecificGroups.PSL3.LinearThreeLocalCores
public import Theory.SpecificGroups.SL2.Affine.Structure
public import Theory.GroupTheory.SolvableResidual

/-!+# Perfectness and generalized Fitting subgroups of the degree-three locals

The vector and covector stabilizers in SL₃(F), and their actual images in
PSL₃(F), are isomorphic to F² ⋊ SL₂(F). Transporting affine perfectness
shows that all four groups equal their solvable residuals when |F| ≥ 4.
In characteristic two their generalized Fitting subgroups are precisely
the root-plane two-cores identified in `LinearThreeLocalCores`.

These are intrinsic local-group facts. The natural-block interpretation
belongs to Chapter C/F and is assembled there from these structural facts
and the literal affine coordinates.

Source: Aschbacher–Smith, F.1.12(I)(1),(II), printed pp.262–264;
the generalized Fitting condition occurs in C.1.7, printed p.123.
-/

public section

namespace Matrix.PSL3.LinearThree

variable (F : Type*) [Field F] [Finite F]

/-- The vector stabilizer in SL₃ is perfect over a field with at least four elements. -/
theorem pointLocalSL_isPerfect (hcard : 4 ≤ Nat.card F) :
    Group.IsPerfect (pointLocalSL F) :=
  Matrix.SL2.isPerfect_of_equiv_affine F hcard (pointLocalAffineEquiv F)

/-- The covector stabilizer in SL₃ is perfect over a field with at least four elements. -/
theorem lineLocalSL_isPerfect (hcard : 4 ≤ Nat.card F) :
    Group.IsPerfect (lineLocalSL F) :=
  Matrix.SL2.isPerfect_of_equiv_affine F hcard (lineLocalAffineEquiv F)

/-- The actual projective point local is perfect. -/
theorem pointLocal_isPerfect (hcard : 4 ≤ Nat.card F) :
    Group.IsPerfect (pointLocal F) :=
  Matrix.SL2.isPerfect_of_equiv_affine F hcard (pointLocalEquivAffine F)

/-- The actual projective line local is perfect. -/
theorem lineLocal_isPerfect (hcard : 4 ≤ Nat.card F) :
    Group.IsPerfect (lineLocal F) :=
  Matrix.SL2.isPerfect_of_equiv_affine F hcard (lineLocalEquivAffine F)

theorem pointLocalSL_solvableResidual_eq_top (hcard : 4 ≤ Nat.card F) :
    Subgroup.solvableResidual (pointLocalSL F) = ⊤ := by
  let := pointLocalSL_isPerfect F hcard
  exact Subgroup.solvableResidual_eq_top

theorem lineLocalSL_solvableResidual_eq_top (hcard : 4 ≤ Nat.card F) :
    Subgroup.solvableResidual (lineLocalSL F) = ⊤ := by
  let := lineLocalSL_isPerfect F hcard
  exact Subgroup.solvableResidual_eq_top

/-- The point-local equality L = L∞ in F.1.12(II)(i). -/
theorem pointLocal_solvableResidual_eq_top (hcard : 4 ≤ Nat.card F) :
    Subgroup.solvableResidual (pointLocal F) = ⊤ := by
  let := pointLocal_isPerfect F hcard
  exact Subgroup.solvableResidual_eq_top

/-- The line-local equality L = L∞ in F.1.12(II)(i). -/
theorem lineLocal_solvableResidual_eq_top (hcard : 4 ≤ Nat.card F) :
    Subgroup.solvableResidual (lineLocal F) = ⊤ := by
  let := lineLocal_isPerfect F hcard
  exact Subgroup.solvableResidual_eq_top

variable [CharP F 2]

theorem pointLocalSL_generalizedFitting_eq_twoCore :
    Theory.GroupTheory.generalizedFitting (pointLocalSL F) = pCore 2 (pointLocalSL F) :=
  Matrix.SL2.generalizedFitting_eq_twoCore_of_equiv_affine F (pointLocalAffineEquiv F)

theorem lineLocalSL_generalizedFitting_eq_twoCore :
    Theory.GroupTheory.generalizedFitting (lineLocalSL F) = pCore 2 (lineLocalSL F) :=
  Matrix.SL2.generalizedFitting_eq_twoCore_of_equiv_affine F (lineLocalAffineEquiv F)

/-- The point local satisfies the generalized Fitting clause of shortness. -/
theorem pointLocal_generalizedFitting_eq_twoCore :
    Theory.GroupTheory.generalizedFitting (pointLocal F) = pCore 2 (pointLocal F) :=
  Matrix.SL2.generalizedFitting_eq_twoCore_of_equiv_affine F (pointLocalEquivAffine F)

/-- The line local satisfies the generalized Fitting clause of shortness. -/
theorem lineLocal_generalizedFitting_eq_twoCore :
    Theory.GroupTheory.generalizedFitting (lineLocal F) = pCore 2 (lineLocal F) :=
  Matrix.SL2.generalizedFitting_eq_twoCore_of_equiv_affine F (lineLocalEquivAffine F)

end Matrix.PSL3.LinearThree
