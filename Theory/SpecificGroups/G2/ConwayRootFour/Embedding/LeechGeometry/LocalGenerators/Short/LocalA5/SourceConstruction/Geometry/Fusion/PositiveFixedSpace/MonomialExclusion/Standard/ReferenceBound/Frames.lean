module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.ReferenceBound.Frames.Batch00
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.ReferenceBound.Frames.Batch01
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.ReferenceBound.Frames.Batch02
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.ReferenceBound.Frames.Batch03
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.ReferenceBound.Frames.Batch04
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.ReferenceBound.Frames.Batch05
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.ReferenceBound.Frames.Batch06
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.ReferenceBound.Frames.Batch07

/-!
# Eight independent common fixed vectors for every reference candidate

The 512 candidates are covered by eight checked batches. Shared Boolean parity
and integral residue checks construct actual matrices of vectors and left inverses;
they imply all three equations of `EightFrame`. This proves the finite arithmetic
obligation without assuming coverage of the candidate table by monomials.

Source context: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284,
and the root-four convention on p.269. Candidate coverage remains with the
independent coverage task and the original reference-bound assembly owner.
-/

open Atlas.Codes Atlas.Lattices
@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.ReferenceBound

/-- All 512 entries have eight independent common fixed vectors. -/
theorem candidateFrames : CandidateFrames := by
  have batches (q : Fin 8) (t : Fin 64) :
      Nonempty (EightFrame referenceMatrix
        (candidateMatrix ⟨64 * q.val + t.val, by omega⟩)) := by
    fin_cases q
    · exact FrameCheck.batch0_frames t
    · exact FrameCheck.batch1_frames t
    · exact FrameCheck.batch2_frames t
    · exact FrameCheck.batch3_frames t
    · exact FrameCheck.batch4_frames t
    · exact FrameCheck.batch5_frames t
    · exact FrameCheck.batch6_frames t
    · exact FrameCheck.batch7_frames t
  intro r
  have h := batches ⟨r.val / 64, by omega⟩ ⟨r.val % 64, by omega⟩
  have he : (⟨64 * (r.val / 64) + r.val % 64, by omega⟩ : Fin 512) = r := by
    apply Fin.ext
    change 64 * (r.val / 64) + r.val % 64 = r.val
    omega
  simpa only [he] using h

/-- The finite arithmetic bound for any actual monomial with a listed parameter pair. -/
theorem commonKernel_bound_of_candidate (a b m : GolayMonomialGroup) (r : Fin 512)
    (hp : ReferenceQuaternionPair a b) (hm : CandidateMatches m r) :
    8 ≤ Module.finrank Bit (StandardCoordinates.commonKernel a m) := by
  obtain ⟨frame⟩ := candidateFrames r
  exact commonKernel_bound_of_frame a b m r hp hm frame

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.ReferenceBound
