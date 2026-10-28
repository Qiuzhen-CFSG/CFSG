/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianProjectiveAngles.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
Source revision: 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianRootPointAngleLevels
public import Theory.AtlasPort.Janko2.Conway.IcosianProjectiveGeometryTransport

/-!
# IcosianProjectiveAngles

Hermitian angles descend to the sign quotient and are invariant under its action.
Lifting quotient elements reduces invariance to the full linear Hermitian group.

Source: Gerald Höhn, `Atlas/Conway/IcosianProjectiveAngles.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and the definition bodies
needed by the source coordinate calculations; source statements are preserved.
-/

public section

noncomputable section
namespace Atlas.Conway

theorem icosianRootPointAngle_projective_smul (g : IcosianProjectiveModel)
    (p q : IcosianRootPoint) :
    icosianRootPointAngle (g • p) (g • q) = icosianRootPointAngle p q := by
  obtain ⟨c,rfl⟩ := icosianProjectiveProjection_surjective g
  rw [icosianProjectivePointAction_mk,icosianProjectivePointAction_mk]
  exact icosianRootPointAngle_smul c p q

theorem icosianRootPointAngle_projective_stabilizer (p q : IcosianRootPoint)
    (g : MulAction.stabilizer IcosianProjectiveModel p) :
    icosianRootPointAngle p (g • q) = icosianRootPointAngle p q := by
  have h := icosianRootPointAngle_projective_smul g.val p q
  rw [g.property] at h
  exact h

end Atlas.Conway
