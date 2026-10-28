module

public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyCertificate.defPairData00
public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyCertificate.defPairData01
public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyCertificate.defPairData02
public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyCertificate.defPairData03

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2Five/AtlasBoundThirtySource/GenerateCertificate.py`.
Source: the thirty retained ATLAS words; see `AtlasBoundThirtySource/README.md`. -/

@[expose] public section
namespace G2Five.AtlasPresentation.ThirtyCertificate
open Subgroup.CosetWordCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
def defPair : Nat → Nat × Letter (Fin 3) :=
  (lookupBranch 1792 (lookupBranch 896 (lookupBranch 384 (lookupBranch 128 defPair0 (lookupBranch 256 defPair128 defPair256)) (lookupBranch 640 (lookupBranch 512 defPair384 defPair512) (lookupBranch 768 defPair640 defPair768))) (lookupBranch 1280 (lookupBranch 1024 defPair896 (lookupBranch 1152 defPair1024 defPair1152)) (lookupBranch 1536 (lookupBranch 1408 defPair1280 defPair1408) (lookupBranch 1664 defPair1536 defPair1664)))) (lookupBranch 2688 (lookupBranch 2176 (lookupBranch 1920 defPair1792 (lookupBranch 2048 defPair1920 defPair2048)) (lookupBranch 2432 (lookupBranch 2304 defPair2176 defPair2304) (lookupBranch 2560 defPair2432 defPair2560))) (lookupBranch 3072 (lookupBranch 2816 defPair2688 (lookupBranch 2944 defPair2816 defPair2944)) (lookupBranch 3328 (lookupBranch 3200 defPair3072 defPair3200) (lookupBranch 3456 defPair3328 defPair3456)))))

end G2Five.AtlasPresentation.ThirtyCertificate
