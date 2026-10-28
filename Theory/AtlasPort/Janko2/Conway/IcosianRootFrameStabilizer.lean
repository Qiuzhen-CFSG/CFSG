/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianRootFrameStabilizer.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianFiveAxisFrames
public import Theory.AtlasPort.Janko2.Conway.IcosianRootFrameAction
public import Theory.AtlasPort.Janko2.Conway.IcosianFullFrameStabilizer

/-!
# IcosianRootFrameStabilizer

Forgetting root-membership witnesses identifies the coordinate root frame with the
projective coordinate-axis frame. Their full stabilizers coincide and have order
2304.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianRootFrameStabilizer.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open scoped Pointwise
attribute [local instance] Classical.propDecidable

/-- Forget only the root-line membership witnesses in an actual frame. -/
def icosianRootFrameSet (F : IcosianRootFrame) : Set IcosianQuaternionPoint :=
  Subtype.val '' (↑F.val : Set IcosianRootPoint)

theorem icosianRootFrameSet_injective : Function.Injective icosianRootFrameSet := by
  intro F G h
  apply Subtype.ext
  apply Finset.coe_injective
  exact Set.image_injective.mpr Subtype.val_injective h

theorem icosianRootFrameSet_smul (g : icosianHermitianGroup) (F : IcosianRootFrame) :
    icosianRootFrameSet (g • F)=g • icosianRootFrameSet F := by
  change Subtype.val '' (↑(g • F.val) : Set IcosianRootPoint)=
    g • (Subtype.val '' (↑F.val : Set IcosianRootPoint))
  rw [Finset.coe_smul_finset]
  exact Set.image_smul_comm (fun p : IcosianRootPoint => p.val) g _ (fun _ => rfl)

/-- The new actual-root frame and the retained coordinate-axis frame are exactly the same projective set. -/
theorem icosianLocalCoordinateRootFrame_set :
    icosianRootFrameSet icosianLocalCoordinateRootFrame=icosianCoordinateFrame := by
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    change q∈({icosianRootAxisPoint 0,icosianRootAxisPoint 1,icosianRootAxisPoint 2} : Finset IcosianRootPoint) at hq
    simp only [Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · exact ⟨0,icosianRootAxisPoint_val 0 |>.symm⟩
    · exact ⟨1,icosianRootAxisPoint_val 1 |>.symm⟩
    · exact ⟨2,icosianRootAxisPoint_val 2 |>.symm⟩
  · rintro ⟨i,rfl⟩
    refine ⟨icosianRootAxisPoint i,?_,icosianRootAxisPoint_val i⟩
    change icosianRootAxisPoint i∈({icosianRootAxisPoint 0,icosianRootAxisPoint 1,icosianRootAxisPoint 2} : Finset IcosianRootPoint)
    fin_cases i <;> simp

/-- The full stabilizer of the actual root frame is the already proved full2304-element monomial stabilizer. -/
theorem icosianLocalCoordinateRootFrame_stabilizer :
    MulAction.stabilizer icosianHermitianGroup icosianLocalCoordinateRootFrame=
      icosianCoordinateFrameStabilizer := by
  ext g
  change g • icosianLocalCoordinateRootFrame=icosianLocalCoordinateRootFrame ↔
    g • icosianCoordinateFrame=icosianCoordinateFrame
  constructor
  · intro h
    rw [← icosianLocalCoordinateRootFrame_set,← icosianRootFrameSet_smul,h]
  · intro h
    apply icosianRootFrameSet_injective
    rw [icosianRootFrameSet_smul,icosianLocalCoordinateRootFrame_set,h]

theorem icosianLocalCoordinateRootFrame_stabilizer_card :
    Nat.card (MulAction.stabilizer icosianHermitianGroup icosianLocalCoordinateRootFrame)=2304 := by
  rw [icosianLocalCoordinateRootFrame_stabilizer,icosianCoordinateFrameStabilizer_card]

end Atlas.Conway
