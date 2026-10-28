/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianFiveAxisFrames.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianAxisNeighborCatalogue
public import Theory.AtlasPort.Janko2.Combinatorics.UniqueTriangleFrames

/-!
# IcosianFiveAxisFrames

There are five explicit orthogonal frames through the first axis. The ten-neighbor
catalogue and unique orthogonal partners prove exhaustiveness.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianFiveAxisFrames.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices Atlas.Combinatorics

def icosianEightPartnerIndex (i : Fin 8) : Fin 8 := ⟨7-i.val,by omega⟩

theorem icosianEightNeighborScalar_partner (i : Fin 8) :
    (icosianEightNeighborScalar (icosianEightPartnerIndex i)).val= -(icosianEightNeighborScalar i).val := by
  fin_cases i <;> apply QuaternionAlgebra.ext <;> decide +kernel

theorem icosianEightNeighborRoot_partner (i : Fin 8) :
    icosianEightNeighborRoot (icosianEightPartnerIndex i)=
      icosianEdgeRootBase (icosianEdgePartner (icosianEightNeighborPair i)) := by
  apply Subtype.ext
  funext j
  apply Subtype.ext
  fin_cases j
  · rfl
  · rfl
  · exact icosianEightNeighborScalar_partner i

theorem icosianEightNeighborPoint_orthogonal_partner (i : Fin 8) :
    IcosianRootPointOrthogonal (icosianEightNeighborPoint i).val
      (icosianEightNeighborPoint (icosianEightPartnerIndex i)).val := by
  change IcosianRootPointOrthogonal (icosianRootToPoint (icosianEightNeighborRoot i))
    (icosianRootToPoint (icosianEightNeighborRoot (icosianEightPartnerIndex i)))
  rw [icosianRootPointOrthogonal_iff,icosianEightNeighborRoot_partner]
  exact icosianEdgeRootBase_orthogonal_partner (icosianEightNeighborPair i)

def icosianFirstFourIndex (i : Fin 4) : Fin 8 := ⟨i.val,by omega⟩

def icosianLocalCoordinateRootFrame : IcosianRootFrame :=
  relationTriangleOfTriple IcosianRootPointOrthogonal
    (fun _ _ => icosianRootPointOrthogonal_symm) icosianRootPointOrthogonal_irrefl
    (icosianRootAxisPoint 0) (icosianRootAxisPoint 1) (icosianRootAxisPoint 2)
    (icosianRootAxisPoints_orthogonal 0 1 (by decide))
    (icosianRootAxisPoints_orthogonal 0 2 (by decide))
    (icosianRootAxisPoints_orthogonal 1 2 (by decide))

def icosianLocalEdgeRootFrame (i : Fin 4) : IcosianRootFrame :=
  relationTriangleOfTriple IcosianRootPointOrthogonal
    (fun _ _ => icosianRootPointOrthogonal_symm) icosianRootPointOrthogonal_irrefl
    (icosianRootAxisPoint 0) (icosianEightNeighborPoint (icosianFirstFourIndex i)).val
    (icosianEightNeighborPoint (icosianEightPartnerIndex (icosianFirstFourIndex i))).val
    (icosianEightNeighborPoint _).property (icosianEightNeighborPoint _).property
    (icosianEightNeighborPoint_orthogonal_partner _)

/-- The coordinate frame and four explicitly constructed edge frames. -/
def icosianFiveAxisFrames : (Unit ⊕ Fin 4) → IcosianRootFrame :=
  Sum.elim (fun _ => icosianLocalCoordinateRootFrame) icosianLocalEdgeRootFrame

theorem icosianFiveAxisFrames_contains_axis (i : Unit ⊕ Fin 4) :
    icosianRootAxisPoint 0∈(icosianFiveAxisFrames i).val := by
  cases i <;> simp [icosianFiveAxisFrames,icosianLocalCoordinateRootFrame,
    icosianLocalEdgeRootFrame,relationTriangleOfTriple]

theorem icosianAxis_frame_pair_unique (p : IcosianAxisNeighbor) (F G : IcosianRootFrame)
    (hF0 : icosianRootAxisPoint 0∈F.val) (hFp : p.val∈F.val)
    (hG0 : icosianRootAxisPoint 0∈G.val) (hGp : p.val∈G.val) : F=G := by
  obtain ⟨B,hB,hu⟩ := unique_triangle_through_pair_of_completion IcosianRootPointOrthogonal
    (fun _ _ => icosianRootPointOrthogonal_symm) icosianRootPointOrthogonal_irrefl
    (icosianRootAxisPoint 0) p.val p.property (icosianRootAxis_completion p)
  exact (hu F ⟨hF0,hFp⟩).trans (hu G ⟨hG0,hGp⟩).symm

theorem icosianEightNeighbor_in_localFrame (i : Fin 8) :
    ∃ j : Fin 4,(icosianEightNeighborPoint i).val∈(icosianLocalEdgeRootFrame j).val := by
  have hi : ∃ j : Fin 4,i=icosianFirstFourIndex j ∨ i=icosianEightPartnerIndex (icosianFirstFourIndex j) := by
    fin_cases i
    · exact ⟨0,Or.inl rfl⟩
    · exact ⟨1,Or.inl rfl⟩
    · exact ⟨2,Or.inl rfl⟩
    · exact ⟨3,Or.inl rfl⟩
    · exact ⟨3,Or.inr rfl⟩
    · exact ⟨2,Or.inr rfl⟩
    · exact ⟨1,Or.inr rfl⟩
    · exact ⟨0,Or.inr rfl⟩
  obtain ⟨j,hj | hj⟩ := hi
  · exact ⟨j,by rw [hj]; simp [icosianLocalEdgeRootFrame,relationTriangleOfTriple]⟩
  · exact ⟨j,by rw [hj]; simp [icosianLocalEdgeRootFrame,relationTriangleOfTriple]⟩

/-- Exhaustion of all actual frames containing the first coordinate axis. -/
theorem icosianFiveAxisFrames_exhaust (F : IcosianRootFrame)
    (hF : icosianRootAxisPoint 0∈F.val) : ∃ i,icosianFiveAxisFrames i=F := by
  classical
  obtain ⟨p,hp,hp0⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show ({icosianRootAxisPoint 0} : Finset IcosianRootPoint).card<F.val.card by rw [F.property.1]; simp)
  have hne : icosianRootAxisPoint 0≠p := by intro he; apply hp0; simp [he]
  let q : IcosianAxisNeighbor := ⟨p,F.property.2 hF hp hne⟩
  obtain ⟨i,hi⟩ := icosianAxisNeighborCatalogue_bijective.surjective q
  cases i with
  | inl j =>
    refine ⟨Sum.inl (),icosianAxis_frame_pair_unique q _ F ?_ ?_ hF hp⟩
    · exact icosianFiveAxisFrames_contains_axis _
    · have he : (icosianTwoAxisNeighbor j).val=p := congrArg Subtype.val hi
      change p∈(icosianFiveAxisFrames (Sum.inl ())).val
      rw [← he]
      fin_cases j <;> simp [icosianFiveAxisFrames,icosianLocalCoordinateRootFrame,
        relationTriangleOfTriple,icosianTwoAxisNeighbor]
  | inr j =>
    obtain ⟨k,hk⟩ := icosianEightNeighbor_in_localFrame j
    refine ⟨Sum.inr k,icosianAxis_frame_pair_unique q _ F ?_ ?_ hF hp⟩
    · exact icosianFiveAxisFrames_contains_axis _
    · exact (congrArg Subtype.val hi) ▸ hk

end Atlas.Conway
