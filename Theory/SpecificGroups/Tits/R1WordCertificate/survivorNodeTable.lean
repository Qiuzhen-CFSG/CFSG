module

public import Theory.SpecificGroups.Tits.R1WordCertificate.survivorNodeData00

/-! Generated kernel certificate; reproduce with `refs/original/n-group-global/parrott-r1-word-certificate/generate.py`.
Source: Parrott (1972), §5, p. 683; see `parrott-tits-presentation.md`. -/

@[expose] public section
namespace Tits.R1WordCertificate
open Subgroup.CosetWordCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
def survivorNode : Nat → Nat :=
  (lookupBranch 512 (lookupBranch 256 (lookupBranch 128 survivorNode0 survivorNode128) (lookupBranch 384 survivorNode256 survivorNode384)) (lookupBranch 768 (lookupBranch 640 survivorNode512 survivorNode640) (lookupBranch 896 survivorNode768 survivorNode896)))

end Tits.R1WordCertificate
