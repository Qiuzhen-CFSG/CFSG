/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
The Iwasawa assembly follows Atlas/LinearGroups/Orthogonal/SimplicityAllCharD.lean,
revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917. Changes: binary singular
vectors, the existing CFSG carrier, and primitivity proved by checked coordinate
root traces.
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.BinaryEightObstruction.Simplicity.Perfect
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.BinaryEightObstruction.Simplicity.Geometry
public import Theory.AtlasPort.GroupTheory.G2IwasawaStabilizer

/-!
# Simplicity of the exact binary split-eight quotient

The faithful natural action and normal abelian root subgroup are constructed
in `Simplicity.Basic`. Coordinate root commutators prove perfectness from
transitivity in `Simplicity.Perfect`. The checked singular-vector and stabilizer
orbits in `Simplicity.Geometry` prove primitivity of this particular action.
Iwasawa's argument then gives simplicity. The last step uses the literal scalar
quotient map defining `POmegaPlus 4 (ZMod 2)`.

The final theorem `isSimpleGroup` discharges the geometric premise of the
retained conditional reductions. It supplies intrinsic simplicity of the
Ω₈⁺(2) carrier used for the section in GLS3 Table 5.3l and the
Aschbacher–Smith A.2.15(2), A.2.19 application.
-/

public noncomputable section
namespace ClassicalOrthogonal.BinaryEightObstruction

/-- Nontriviality follows from the already proved noncommuting binary roots. -/
theorem projective_nontrivial : Nontrivial (POmegaPlus 4 (ZMod 2)) := by
  apply not_subsingleton_iff_nontrivial.mp
  intro h
  let := h
  exact not_isMulCommutative inferInstance

namespace Simplicity

/-- All algebraic inputs to Iwasawa are discharged; only the natural action's
geometric primitivity remains as an explicit premise. -/
theorem elementary_simple_of_preprimitive [MulAction.IsPreprimitive E Point] :
    IsSimpleGroup E := by
  let : Group.IsPerfect E := perfect_of_pretransitive
  let : Nontrivial (POmegaPlus 4 K) := projective_nontrivial
  let : Nontrivial E := (projectiveElementaryMap_surjective Q).nontrivial
  exact Atlas.GroupTheory.iwasawa_stabilizer_simple (pointE 0) (rootGroup (pointE 0))
    (rootGroup_le_stabilizer (pointE 0)) (rootGroup_normal_stabilizer (pointE 0))
    inferInstance (rootGroup_normalClosure (pointE 0))

end Simplicity

/-- Simplicity transported through the exact scalar quotient map, with the
geometric premise retained for compatibility with the conditional reduction. -/
theorem isSimpleGroup_of_preprimitive
    [MulAction.IsPreprimitive Simplicity.E Simplicity.Point] :
    IsSimpleGroup (POmegaPlus 4 (ZMod 2)) := by
  let : IsSimpleGroup Simplicity.E := Simplicity.elementary_simple_of_preprimitive
  let : Nontrivial (POmegaPlus 4 (ZMod 2)) := projective_nontrivial
  exact IsSimpleGroup.isSimpleGroup_of_surjective (projectiveElementaryMap Simplicity.Q)
    (projectiveElementaryMap_surjective Simplicity.Q)

/-- Intrinsic simplicity of the Siegel-generated split-eight orthogonal group
over the binary field, modulo its scalar subgroup. All geometric and algebraic
inputs are proved for this exact carrier. -/
theorem isSimpleGroup : IsSimpleGroup (POmegaPlus 4 (ZMod 2)) := by
  let : MulAction.IsPreprimitive Simplicity.E Simplicity.Point :=
    Simplicity.singular_preprimitive
  exact isSimpleGroup_of_preprimitive

end ClassicalOrthogonal.BinaryEightObstruction
