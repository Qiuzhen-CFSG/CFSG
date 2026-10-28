/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianProjectiveGeometryTransport.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianProjectiveModel
public import Mathlib.GroupTheory.GroupAction.Primitive

/-!
# IcosianProjectiveGeometryTransport

The surjective sign-quotient projection preserves the root-point action. It
identifies point-stabilizer orbits and transfers primitivity to the quotient.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianProjectiveGeometryTransport.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


noncomputable section
namespace Atlas.Conway
open MulAction

theorem icosianProjectiveProjection_surjective :
    Function.Surjective icosianProjectiveProjection := QuotientGroup.mk'_surjective _

/-- Full point-stabilizer orbits are unchanged by passing to the actual sign
quotient. Every quotient stabilizer element lifts to the full linear stabilizer. -/
theorem icosianProjectiveStabilizer_orbit (p q : IcosianRootPoint) :
    orbit (stabilizer IcosianProjectiveModel p) q=
      orbit (stabilizer icosianHermitianGroup p) q := by
  ext r
  constructor
  · rintro ⟨g,rfl⟩
    obtain ⟨c,hc⟩ := icosianProjectiveProjection_surjective g.val
    have hn : c∈stabilizer icosianHermitianGroup p := by
      change c • p=p
      rw [← icosianProjectivePointAction_mk,hc]
      exact g.property
    refine ⟨⟨c,hn⟩,?_⟩
    change c • q=g.val • q
    rw [← icosianProjectivePointAction_mk,hc]
  · rintro ⟨g,rfl⟩
    have hn : icosianProjectiveProjection g.val∈stabilizer IcosianProjectiveModel p := by
      change icosianProjectiveProjection g.val • p=p
      rw [icosianProjectivePointAction_mk]
      exact g.property
    refine ⟨⟨icosianProjectiveProjection g.val,hn⟩,?_⟩
    exact icosianProjectivePointAction_mk g.val q

theorem icosianProjective_primitive_of_linear
    [IsPreprimitive icosianHermitianGroup IcosianRootPoint] :
    IsPreprimitive IcosianProjectiveModel IcosianRootPoint := by
  let f : IcosianRootPoint →ₑ[icosianProjectiveProjection] IcosianRootPoint :=
    ⟨id,fun g p => (icosianProjectivePointAction_mk g p).symm⟩
  exact IsPreprimitive.of_surjective (f := f) Function.surjective_id

end Atlas.Conway
