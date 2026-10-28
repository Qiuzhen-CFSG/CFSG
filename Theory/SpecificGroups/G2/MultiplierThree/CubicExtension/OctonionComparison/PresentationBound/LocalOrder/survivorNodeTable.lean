module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.survivorNodeData00
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.survivorNodeData01

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

@[expose] public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

def survivorNode : Nat → Nat :=
  (lookupBranch 640 (lookupBranch 256 (lookupBranch 128 survivorNode0 survivorNode128) (lookupBranch 384 survivorNode256 (lookupBranch 512 survivorNode384 survivorNode512))) (lookupBranch 1024 (lookupBranch 768 survivorNode640 (lookupBranch 896 survivorNode768 survivorNode896)) (lookupBranch 1152 survivorNode1024 (lookupBranch 1280 survivorNode1152 survivorNode1280))))

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
