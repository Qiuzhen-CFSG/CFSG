/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianAxisOrbitLinks.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianAxisOrbitLinkShapes
public import Theory.AtlasPort.Janko2.Conway.IcosianAxisTransitionImages

/-!
# IcosianAxisOrbitLinks

Explicit reflection words join the local monomial orbits with the same coordinate
norm. These links assemble the full axis-stabilizer orbits.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianAxisOrbitLinks.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

theorem icosianAxisOrbit_B_C (p q : IcosianRootPoint)
    (hp : HasIcosianRootPointShape p 1) (hq : HasIcosianRootPointShape q 2)
    (hnp : icosianRootPointNormWord p 0=2) (hnq : icosianRootPointNormWord q 0=2) :
    IcosianSameAxisOrbit p q := by
  let r := icosianAxisLinkBInput
  let s := icosianAxisTransitionWord 0 • r
  apply icosianSameAxisOrbit_transport (icosianRootToPoint r) (icosianRootToPoint s)
    (v:=2) (p:=p) (q:=q)
  · exact ⟨r,rfl,icosianAxisLinkBInput_shape⟩
  · exact ⟨s,rfl,icosianAxisLinkBImage_shape⟩
  · rw [icosianRootPointNormWord_toPoint]; exact icosianAxisLinkBInput_norm
  · rw [icosianRootPointNormWord_toPoint]; exact icosianAxisLinkBImage_word 0
  · apply icosianSameAxisOrbit_of_map (icosianAxisTransitionWord 0)
      (icosianAxisTransitionWord_fixes_axis 0)
    exact (icosianRootToPoint_smul _ _).symm
  · exact hp
  · exact hq
  · exact hnp
  · exact hnq

theorem icosianAxisOrbit_C_D (p q : IcosianRootPoint)
    (hp : HasIcosianRootPointShape p 2) (hq : HasIcosianRootPointShape q 3)
    (hnp : icosianRootPointNormWord p 0=1) (hnq : icosianRootPointNormWord q 0=1) :
    IcosianSameAxisOrbit p q := by
  let r := icosianAxisLinkCInput
  let s := icosianAxisTransitionWord 1 • r
  apply icosianSameAxisOrbit_transport (icosianRootToPoint r) (icosianRootToPoint s)
    (v:=1) (p:=p) (q:=q)
  · exact ⟨r,rfl,icosianAxisLinkCInput_shape⟩
  · exact ⟨s,rfl,icosianAxisLinkCImage_shape⟩
  · rw [icosianRootPointNormWord_toPoint]; exact icosianAxisLinkCInput_norm
  · rw [icosianRootPointNormWord_toPoint]; exact icosianAxisLinkCImage_word 0
  · apply icosianSameAxisOrbit_of_map (icosianAxisTransitionWord 1)
      (icosianAxisTransitionWord_fixes_axis 1)
    exact (icosianRootToPoint_smul _ _).symm
  · exact hp
  · exact hq
  · exact hnp
  · exact hnq

theorem icosianAxisOrbit_A_B (p q : IcosianRootPoint)
    (hp : HasIcosianRootPointShape p 0) (hq : HasIcosianRootPointShape q 1)
    (hnp : icosianRootPointNormWord p 0=0) (hnq : icosianRootPointNormWord q 0=0) :
    IcosianSameAxisOrbit p q := by
  let r := icosianAxisRoot (1,1)
  let s := icosianEightNeighborRoot 1
  have hs : HasIcosianRootShape s 1 := by
    apply (icosianRootShape_edge _).mpr
    apply icosianEdgeRoot_recognition _ 0
    · exact icosianEdgeRootBase_zero _
    · exact icosianEdgeRootBase_norm _
  have hnr : icosianRootNormWord r 0=0 := by
    apply icosianRootNormWord_of_norm
    simp [r,icosianAxisRoot,icosianSingle,icosianNorm]
  have hns : icosianRootNormWord s 0=0 := by
    apply icosianRootNormWord_of_norm
    change icosianNorm (0 : IcosianQuaternion)=goldenIntegerToRational 0
    simp [icosianNorm]
  apply icosianSameAxisOrbit_transport (icosianRootToPoint r) (icosianRootToPoint s)
    (v:=0) (p:=p) (q:=q)
  · exact ⟨r,rfl,(icosianRootShape_axis _).mpr (icosianAxisRoot_axis (1,1))⟩
  · exact ⟨s,rfl,hs⟩
  · simpa only [icosianRootPointNormWord_toPoint] using hnr
  · simpa only [icosianRootPointNormWord_toPoint] using hns
  · apply icosianSameAxisOrbit_of_map (icosianAxisTransitionWord 0)
      (icosianAxisTransitionWord_fixes_axis 0)
    exact icosianAxisTransitionWord_axis 0 1
  · exact hp
  · exact hq
  · exact hnp
  · exact hnq

end Atlas.Conway
