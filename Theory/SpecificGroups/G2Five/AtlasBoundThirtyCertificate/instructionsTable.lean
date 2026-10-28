module

public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyCertificate.instructionsData00
public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyCertificate.instructionsData01
public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyCertificate.instructionsData02
public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyCertificate.instructionsData03
public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyCertificate.instructionsData04
public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyCertificate.instructionsData05
public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyCertificate.instructionsData06
public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyCertificate.instructionsData07

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2Five/AtlasBoundThirtySource/GenerateCertificate.py`.
Source: the thirty retained ATLAS words; see `AtlasBoundThirtySource/README.md`. -/

@[expose] public section
namespace G2Five.AtlasPresentation.ThirtyCertificate
open Subgroup.CosetWordCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
def instructions : Nat → Instruction (Fin 3) :=
  (lookupBranch 3968 (lookupBranch 1920 (lookupBranch 896 (lookupBranch 384 (lookupBranch 128 instructions0 (lookupBranch 256 instructions128 instructions256)) (lookupBranch 640 (lookupBranch 512 instructions384 instructions512) (lookupBranch 768 instructions640 instructions768))) (lookupBranch 1408 (lookupBranch 1152 (lookupBranch 1024 instructions896 instructions1024) (lookupBranch 1280 instructions1152 instructions1280)) (lookupBranch 1664 (lookupBranch 1536 instructions1408 instructions1536) (lookupBranch 1792 instructions1664 instructions1792)))) (lookupBranch 2944 (lookupBranch 2432 (lookupBranch 2176 (lookupBranch 2048 instructions1920 instructions2048) (lookupBranch 2304 instructions2176 instructions2304)) (lookupBranch 2688 (lookupBranch 2560 instructions2432 instructions2560) (lookupBranch 2816 instructions2688 instructions2816))) (lookupBranch 3456 (lookupBranch 3200 (lookupBranch 3072 instructions2944 instructions3072) (lookupBranch 3328 instructions3200 instructions3328)) (lookupBranch 3712 (lookupBranch 3584 instructions3456 instructions3584) (lookupBranch 3840 instructions3712 instructions3840))))) (lookupBranch 6016 (lookupBranch 4992 (lookupBranch 4480 (lookupBranch 4224 (lookupBranch 4096 instructions3968 instructions4096) (lookupBranch 4352 instructions4224 instructions4352)) (lookupBranch 4736 (lookupBranch 4608 instructions4480 instructions4608) (lookupBranch 4864 instructions4736 instructions4864))) (lookupBranch 5504 (lookupBranch 5248 (lookupBranch 5120 instructions4992 instructions5120) (lookupBranch 5376 instructions5248 instructions5376)) (lookupBranch 5760 (lookupBranch 5632 instructions5504 instructions5632) (lookupBranch 5888 instructions5760 instructions5888)))) (lookupBranch 7040 (lookupBranch 6528 (lookupBranch 6272 (lookupBranch 6144 instructions6016 instructions6144) (lookupBranch 6400 instructions6272 instructions6400)) (lookupBranch 6784 (lookupBranch 6656 instructions6528 instructions6656) (lookupBranch 6912 instructions6784 instructions6912))) (lookupBranch 7552 (lookupBranch 7296 (lookupBranch 7168 instructions7040 instructions7168) (lookupBranch 7424 instructions7296 instructions7424)) (lookupBranch 7808 (lookupBranch 7680 instructions7552 instructions7680) (lookupBranch 7936 instructions7808 instructions7936))))))

end G2Five.AtlasPresentation.ThirtyCertificate
