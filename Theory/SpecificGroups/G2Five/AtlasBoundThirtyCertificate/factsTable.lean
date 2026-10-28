module

public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyCertificate.factsData00
public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyCertificate.factsData01
public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyCertificate.factsData02
public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyCertificate.factsData03
public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyCertificate.factsData04
public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyCertificate.factsData05
public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyCertificate.factsData06
public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyCertificate.factsData07

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2Five/AtlasBoundThirtySource/GenerateCertificate.py`.
Source: the thirty retained ATLAS words; see `AtlasBoundThirtySource/README.md`. -/

@[expose] public section
namespace G2Five.AtlasPresentation.ThirtyCertificate
open Subgroup.CosetWordCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
def facts : Nat → FactData (Fin 3) :=
  (lookupBranch 3968 (lookupBranch 1920 (lookupBranch 896 (lookupBranch 384 (lookupBranch 128 facts0 (lookupBranch 256 facts128 facts256)) (lookupBranch 640 (lookupBranch 512 facts384 facts512) (lookupBranch 768 facts640 facts768))) (lookupBranch 1408 (lookupBranch 1152 (lookupBranch 1024 facts896 facts1024) (lookupBranch 1280 facts1152 facts1280)) (lookupBranch 1664 (lookupBranch 1536 facts1408 facts1536) (lookupBranch 1792 facts1664 facts1792)))) (lookupBranch 2944 (lookupBranch 2432 (lookupBranch 2176 (lookupBranch 2048 facts1920 facts2048) (lookupBranch 2304 facts2176 facts2304)) (lookupBranch 2688 (lookupBranch 2560 facts2432 facts2560) (lookupBranch 2816 facts2688 facts2816))) (lookupBranch 3456 (lookupBranch 3200 (lookupBranch 3072 facts2944 facts3072) (lookupBranch 3328 facts3200 facts3328)) (lookupBranch 3712 (lookupBranch 3584 facts3456 facts3584) (lookupBranch 3840 facts3712 facts3840))))) (lookupBranch 6016 (lookupBranch 4992 (lookupBranch 4480 (lookupBranch 4224 (lookupBranch 4096 facts3968 facts4096) (lookupBranch 4352 facts4224 facts4352)) (lookupBranch 4736 (lookupBranch 4608 facts4480 facts4608) (lookupBranch 4864 facts4736 facts4864))) (lookupBranch 5504 (lookupBranch 5248 (lookupBranch 5120 facts4992 facts5120) (lookupBranch 5376 facts5248 facts5376)) (lookupBranch 5760 (lookupBranch 5632 facts5504 facts5632) (lookupBranch 5888 facts5760 facts5888)))) (lookupBranch 7040 (lookupBranch 6528 (lookupBranch 6272 (lookupBranch 6144 facts6016 facts6144) (lookupBranch 6400 facts6272 facts6400)) (lookupBranch 6784 (lookupBranch 6656 facts6528 facts6656) (lookupBranch 6912 facts6784 facts6912))) (lookupBranch 7552 (lookupBranch 7296 (lookupBranch 7168 facts7040 facts7168) (lookupBranch 7424 facts7296 facts7424)) (lookupBranch 7808 (lookupBranch 7680 facts7552 facts7680) (lookupBranch 7936 facts7808 facts7936))))))

end G2Five.AtlasPresentation.ThirtyCertificate
