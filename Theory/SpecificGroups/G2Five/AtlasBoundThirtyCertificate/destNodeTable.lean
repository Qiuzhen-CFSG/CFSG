module

public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyCertificate.destNodeData00

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2Five/AtlasBoundThirtySource/GenerateCertificate.py`.
Source: the thirty retained ATLAS words; see `AtlasBoundThirtySource/README.md`. -/

@[expose] public section
namespace G2Five.AtlasPresentation.ThirtyCertificate
open Subgroup.CosetWordCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
def destNode : Nat → Nat :=
  (lookupBranch 128 destNode0 (lookupBranch 256 destNode128 destNode256))

end G2Five.AtlasPresentation.ThirtyCertificate
