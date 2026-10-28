module

public import Theory.SpecificGroups.Lyons.GebhardtParabolicIndexCertificate.defCodeData00

/-! Kernel-checked certificate data for Gebhardt (2000), Section 3B.
Reproduce with `Theory/SpecificGroups/Lyons/GebhardtParabolicIndexCertificate/source/generate.py`. -/

@[expose] public section
namespace Lyons.Gebhardt.ParabolicIndexCertificate
open Subgroup.CosetWordCertificate

def defCode (i : Nat) : Nat :=
  unpack (lookupBranch 160 (lookupBranch 64 (lookupBranch 32 defCodePage0 defCodePage32) (lookupBranch 96 defCodePage64 (lookupBranch 128 defCodePage96 defCodePage128))) (lookupBranch 256 (lookupBranch 192 defCodePage160 (lookupBranch 224 defCodePage192 defCodePage224)) (lookupBranch 288 defCodePage256 (lookupBranch 320 defCodePage288 defCodePage320)))) 19 i

end Lyons.Gebhardt.ParabolicIndexCertificate
