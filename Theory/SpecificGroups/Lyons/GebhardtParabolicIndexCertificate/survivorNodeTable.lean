module

public import Theory.SpecificGroups.Lyons.GebhardtParabolicIndexCertificate.survivorNodeData00

/-! Kernel-checked certificate data for Gebhardt (2000), Section 3B.
Reproduce with `Theory/SpecificGroups/Lyons/GebhardtParabolicIndexCertificate/source/generate.py`. -/

@[expose] public section
namespace Lyons.Gebhardt.ParabolicIndexCertificate
open Subgroup.CosetWordCertificate

def survivorNode (i : Nat) : Nat :=
  unpack survivorNodePage0 16 i

end Lyons.Gebhardt.ParabolicIndexCertificate
