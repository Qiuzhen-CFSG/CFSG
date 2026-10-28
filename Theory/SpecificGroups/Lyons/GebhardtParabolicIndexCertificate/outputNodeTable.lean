module

public import Theory.SpecificGroups.Lyons.GebhardtParabolicIndexCertificate.outputNodeData00

/-! Kernel-checked certificate data for Gebhardt (2000), Section 3B.
Reproduce with `Theory/SpecificGroups/Lyons/GebhardtParabolicIndexCertificate/source/generate.py`. -/

@[expose] public section
namespace Lyons.Gebhardt.ParabolicIndexCertificate
open Subgroup.CosetWordCertificate

def outputNode (i : Nat) : Nat :=
  unpack (lookupBranch 64 (lookupBranch 32 outputNodePage0 outputNodePage32) (lookupBranch 96 outputNodePage64 (lookupBranch 128 outputNodePage96 outputNodePage128))) 18 i

end Lyons.Gebhardt.ParabolicIndexCertificate
