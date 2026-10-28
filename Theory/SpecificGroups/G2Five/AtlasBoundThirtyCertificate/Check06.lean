module

public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyCertificate.Context
public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyCertificate.factsTable
public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyCertificate.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2Five/AtlasBoundThirtySource/GenerateCertificate.py`.
Source: the thirty retained ATLAS words; see `AtlasBoundThirtySource/README.md`. -/

public section
namespace G2Five.AtlasPresentation.ThirtyCertificate
open Subgroup.CosetWordCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem checked_6144 : checkChunk context facts instructions 6144 1024 = true := by decide +kernel

end G2Five.AtlasPresentation.ThirtyCertificate
