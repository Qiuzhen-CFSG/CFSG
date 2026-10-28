module

public import Theory.SpecificGroups.Thompson.Model.Simplicity.NormalGenerationHigh.Word31Certificate.defPairData00
public import Theory.SpecificGroups.Thompson.Model.Simplicity.NormalGenerationHigh.Word31Certificate.defPairData01

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/Thompson/Model/Simplicity/NormalGenerationHigh/source/generate.py`.
Source word: ATLAS Th conjugacy table, https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/Th/. -/

@[expose] public section
namespace Thompson.Simplicity.Word31Certificate
open Subgroup.CosetWordCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
def defPair : Nat → Nat × Letter (Fin 2) :=
  (lookupBranch 3456 (lookupBranch 1664 (lookupBranch 768 (lookupBranch 384 (lookupBranch 128 defPair0 (lookupBranch 256 defPair128 defPair256)) (lookupBranch 512 defPair384 (lookupBranch 640 defPair512 defPair640))) (lookupBranch 1152 (lookupBranch 896 defPair768 (lookupBranch 1024 defPair896 defPair1024)) (lookupBranch 1408 (lookupBranch 1280 defPair1152 defPair1280) (lookupBranch 1536 defPair1408 defPair1536)))) (lookupBranch 2560 (lookupBranch 2048 (lookupBranch 1792 defPair1664 (lookupBranch 1920 defPair1792 defPair1920)) (lookupBranch 2304 (lookupBranch 2176 defPair2048 defPair2176) (lookupBranch 2432 defPair2304 defPair2432))) (lookupBranch 2944 (lookupBranch 2688 defPair2560 (lookupBranch 2816 defPair2688 defPair2816)) (lookupBranch 3200 (lookupBranch 3072 defPair2944 defPair3072) (lookupBranch 3328 defPair3200 defPair3328))))) (lookupBranch 5120 (lookupBranch 4224 (lookupBranch 3840 (lookupBranch 3584 defPair3456 (lookupBranch 3712 defPair3584 defPair3712)) (lookupBranch 3968 defPair3840 (lookupBranch 4096 defPair3968 defPair4096))) (lookupBranch 4608 (lookupBranch 4352 defPair4224 (lookupBranch 4480 defPair4352 defPair4480)) (lookupBranch 4864 (lookupBranch 4736 defPair4608 defPair4736) (lookupBranch 4992 defPair4864 defPair4992)))) (lookupBranch 6016 (lookupBranch 5504 (lookupBranch 5248 defPair5120 (lookupBranch 5376 defPair5248 defPair5376)) (lookupBranch 5760 (lookupBranch 5632 defPair5504 defPair5632) (lookupBranch 5888 defPair5760 defPair5888))) (lookupBranch 6400 (lookupBranch 6144 defPair6016 (lookupBranch 6272 defPair6144 defPair6272)) (lookupBranch 6656 (lookupBranch 6528 defPair6400 defPair6528) (lookupBranch 6784 defPair6656 defPair6784))))))

end Thompson.Simplicity.Word31Certificate
