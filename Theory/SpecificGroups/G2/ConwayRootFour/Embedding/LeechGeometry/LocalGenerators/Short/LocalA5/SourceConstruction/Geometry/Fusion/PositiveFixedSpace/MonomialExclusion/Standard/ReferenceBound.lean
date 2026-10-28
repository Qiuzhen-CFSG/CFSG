module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.Reference
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.ReferenceBound.Contracts
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.ReferenceBound.Coverage
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.ReferenceBound.Frames

/-!
# Assembly of the reference quaternion kernel bound

The original square and centralization hypotheses imply the literal coordinate
constraints. Exhaustive coverage reconstructs the actual sign and inverse
permutation as one of the 512 candidates. Each candidate has eight common fixed
vectors with a checked left inverse, proving the lower bound in the explicit
coordinates of Λ/2Λ. Both finite obligations are discharged here; normalization
of a general signed quaternion pair remains a separate geometric calculation.

Source context: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284,
and the root-four convention on p.269.
-/

@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion

/-- The two finite obligations feed the exact published reference contract. -/
theorem referenceQuaternionBound_of_coverage_frames
    (hc : ReferenceBound.CandidateCoverage) (hf : ReferenceBound.CandidateFrames) :
    ReferenceQuaternionBound := by
  intro a b m hp hm hma hmb
  obtain ⟨r, hr⟩ := hc m
    (ReferenceBound.centralizerParameters_of_reference a b m hp hm hma hmb)
  obtain ⟨frame⟩ := hf r
  exact ReferenceBound.commonKernel_bound_of_frame a b m r hp hr frame

/-- Every square-one monomial centralizing the literal reference pair has a
common binary kernel of dimension at least eight. -/
theorem referenceQuaternionBound : ReferenceQuaternionBound :=
  referenceQuaternionBound_of_coverage_frames
    ReferenceBound.candidateCoverage ReferenceBound.candidateFrames

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion
