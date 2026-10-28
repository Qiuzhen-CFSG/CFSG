module

public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyCertificate.outputNodeData00

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2Five/AtlasBoundThirtySource/GenerateCertificate.py`.
Source: the thirty retained ATLAS words; see `AtlasBoundThirtySource/README.md`. -/

@[expose] public section
namespace G2Five.AtlasPresentation.ThirtyCertificate
open Subgroup.CosetWordCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
def outputNode : Nat → Nat :=
  (lookupBranch 128 outputNode0 (lookupBranch 256 outputNode128 outputNode256))

end G2Five.AtlasPresentation.ThirtyCertificate
