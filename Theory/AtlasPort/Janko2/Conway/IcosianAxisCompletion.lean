/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianAxisCompletion.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianAxisPairCompletion
public import Theory.AtlasPort.Janko2.Conway.IcosianAxisNeighborCount

/-!
# IcosianAxisCompletion

Every neighbor of the coordinate root line has a unique orthogonal third line. The
axis-pair and edge-root calculations exhaust the possibilities.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianAxisCompletion.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

/-- Every root line perpendicular to the first coordinate axis has exactly one
third root line perpendicular to both. The completion is constructed inside the actual lattice. -/
theorem icosianRootAxis_completion (p : IcosianAxisNeighbor) :
    ∃! q : IcosianRootPoint,
      IcosianRootPointOrthogonal (icosianRootAxisPoint 0) q ∧
      IcosianRootPointOrthogonal p.val q := by
  obtain ⟨r,hr⟩ := icosianRootToPoint_surjective p.val
  have hz := (icosianRootAxisPoint_orthogonal_iff 0 r).mp (hr.symm ▸ p.property)
  rcases icosianRoot_zero_structure r hz with h1 | h2 | hn
  · have hp : p.val=icosianRootAxisPoint 2 := by
      rw [← hr]
      apply icosianRootPoint_of_single_support r 2
      intro i hi
      fin_cases i
      · exact hz
      · exact h1
      · exact (hi rfl).elim
    refine ⟨icosianRootAxisPoint 1,⟨icosianRootAxisPoints_orthogonal 0 1 (by decide),?_⟩,?_⟩
    · rw [hp]
      exact icosianRootAxisPoints_orthogonal 2 1 (by decide)
    · intro q hq
      rw [hp] at hq
      exact icosianRootAxisPair_complement_unique 0 2 1 (by decide) (by decide) (by decide) q hq.1 hq.2
  · have hp : p.val=icosianRootAxisPoint 1 := by
      rw [← hr]
      apply icosianRootPoint_of_single_support r 1
      intro i hi
      fin_cases i
      · exact hz
      · exact (hi rfl).elim
      · exact h2
    refine ⟨icosianRootAxisPoint 2,⟨icosianRootAxisPoints_orthogonal 0 2 (by decide),?_⟩,?_⟩
    · rw [hp]
      exact icosianRootAxisPoints_orthogonal 1 2 (by decide)
    · intro q hq
      rw [hp] at hq
      exact icosianRootAxisPair_complement_unique 0 1 2 (by decide) (by decide) (by decide) q hq.1 hq.2
  · obtain ⟨b,hb⟩ := icosianEdgeRootBase_reconstruct r hz hn.1 hn.2
    have hp : p.val=icosianRootToPoint (icosianEdgeRootBase b) := by rw [hb,hr]
    let s := icosianEdgeRootBase (icosianEdgePartner b)
    refine ⟨icosianRootToPoint s,⟨?_,?_⟩,?_⟩
    · apply (icosianRootAxisPoint_orthogonal_iff 0 s).mpr
      exact icosianEdgeRootBase_zero _
    · rw [hp,icosianRootPointOrthogonal_iff]
      exact icosianEdgeRootBase_orthogonal_partner b
    · intro q hq
      obtain ⟨t,ht⟩ := icosianRootToPoint_surjective q
      have ht0 := (icosianRootAxisPoint_orthogonal_iff 0 t).mp (ht.symm ▸ hq.1)
      have hh := hq.2
      rw [hp,← ht,icosianRootPointOrthogonal_iff] at hh
      rw [← ht]
      apply Subtype.ext
      exact icosianEdgeRootBase_complement_unique b t ht0 hh

end Atlas.Conway
