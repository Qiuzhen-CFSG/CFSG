module

public import Theory.SpecificGroups.Lyons.GebhardtParabolicIndexCertificate.destNodeData00

/-! Kernel-checked certificate data for Gebhardt (2000), Section 3B.
Reproduce with `Theory/SpecificGroups/Lyons/GebhardtParabolicIndexCertificate/source/generate.py`. -/

@[expose] public section
namespace Lyons.Gebhardt.ParabolicIndexCertificate
open Subgroup.CosetWordCertificate

def destNode (i : Nat) : Nat :=
  unpack (lookupBranch 64 (lookupBranch 32 destNodePage0 destNodePage32) (lookupBranch 96 destNodePage64 (lookupBranch 128 destNodePage96 destNodePage128))) 12 i

end Lyons.Gebhardt.ParabolicIndexCertificate
