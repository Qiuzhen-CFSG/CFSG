/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianRootLocalOrbits.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianLocalAOrbit
public import Theory.AtlasPort.Janko2.Conway.IcosianLocalBOrbit
public import Theory.AtlasPort.Janko2.Conway.IcosianLocalDOrbit

/-!
# IcosianRootLocalOrbits

The four root shapes are exactly the full frame-stabilizer orbits. Their individual
orbit calculations assemble the exhaustive, disjoint local orbit catalogue.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianRootLocalOrbits.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


noncomputable section
namespace Atlas.Conway
open Atlas.Lattices
open scoped Matrix

def icosianRootLocalRepresentative : Fin 4 → IcosianRootPoint :=
  ![icosianRootAxisPoint 0,icosianRootToPoint icosianLocalBRoot,
    icosianRootToPoint icosianLocalCRoot,icosianRootToPoint icosianLocalDRoot]

/-- The four norm shapes are exactly the four orbits of the full coordinate
frame stabilizer on all315 actual quaternionic root lines. -/
theorem icosianRootPoint_local_orbit (i : Fin 4) (p : IcosianRootPoint) :
    p∈MulAction.orbit icosianCoordinateFrameStabilizer (icosianRootLocalRepresentative i) ↔
      HasIcosianRootPointShape p i := by
  fin_cases i
  · exact (icosianLocalA_full_frame_orbit p).symm
  · exact (icosianLocalB_full_frame_orbit p).symm
  · exact (icosianLocalC_full_frame_orbit p).symm
  · exact (icosianLocalD_full_frame_orbit p).symm

theorem icosianRootPoint_local_orbit_card (i : Fin 4) :
    Nat.card (MulAction.orbit icosianCoordinateFrameStabilizer
      (icosianRootLocalRepresentative i))=![3,24,192,96] i := by
  have he : MulAction.orbit icosianCoordinateFrameStabilizer (icosianRootLocalRepresentative i)=
      {p : IcosianRootPoint | HasIcosianRootPointShape p i} :=
    Set.ext (icosianRootPoint_local_orbit i)
  rw [Nat.card_congr (Equiv.setCongr he)]
  exact icosianRootPointShape_card i

theorem icosianRootPoint_local_stabilizer_card (i : Fin 4) :
    Nat.card (MulAction.stabilizer icosianCoordinateFrameStabilizer
      (icosianRootLocalRepresentative i))=![768,96,12,24] i := by
  fin_cases i
  · exact icosianLocalA_full_frame_stabilizer_card
  · exact icosianLocalB_full_frame_stabilizer_card
  · exact icosianLocalC_full_frame_stabilizer_card
  · exact icosianLocalD_full_frame_stabilizer_card

theorem icosianRootPoint_local_orbits_exhaustive (p : IcosianRootPoint) :
    ∃ i,p∈MulAction.orbit icosianCoordinateFrameStabilizer (icosianRootLocalRepresentative i) := by
  obtain ⟨i,hi⟩ := icosianRootPointShape_exhaustive p
  exact ⟨i,(icosianRootPoint_local_orbit i p).mpr hi⟩

theorem icosianRootPoint_local_orbits_disjoint (i j : Fin 4) (hij : i≠j) :
    Disjoint (MulAction.orbit icosianCoordinateFrameStabilizer (icosianRootLocalRepresentative i))
      (MulAction.orbit icosianCoordinateFrameStabilizer (icosianRootLocalRepresentative j)) := by
  rw [Set.disjoint_left]
  intro p hi hj
  exact hij (icosianRootPointShape_unique p ((icosianRootPoint_local_orbit i p).mp hi)
    ((icosianRootPoint_local_orbit j p).mp hj))

end Atlas.Conway
