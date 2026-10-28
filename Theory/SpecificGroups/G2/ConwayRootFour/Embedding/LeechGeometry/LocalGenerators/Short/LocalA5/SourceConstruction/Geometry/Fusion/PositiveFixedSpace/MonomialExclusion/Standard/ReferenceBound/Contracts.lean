module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.ReferenceBound.Parameters
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.ReferenceBound.Certificate

/-!
# Independent finite obligations for the reference quaternion calculation

Coverage reconstructs the two literal signed-coordinate parameters from the
explicit candidate table. `CandidateFrames`, supplied by the certificate module,
requires eight independent common fixed vectors for each entry. Neither statement
is proved in this interface. Their assembly retains both as explicit premises.
-/

open Atlas.Lattices
@[expose] public section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.ReferenceBound

/-- Exhaustiveness of the published finite list under the proved coordinate equations. -/
def CandidateCoverage : Prop :=
  ∀ m : GolayMonomialGroup, CentralizerParameters m →
    ∃ r : Fin 512, CandidateMatches m r

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.ReferenceBound
