module

public import Theory.SpecificGroups.Lyons.GebhardtParabolicIndexCertificate.factCodeTable
public import Theory.SpecificGroups.Lyons.GebhardtParabolicIndexCertificate.Words

/-! Kernel-checked certificate data for Gebhardt (2000), Section 3B.
Reproduce with `Theory/SpecificGroups/Lyons/GebhardtParabolicIndexCertificate/source/generate.py`. -/

@[expose] public section
namespace Lyons.Gebhardt.ParabolicIndexCertificate
open Subgroup.CosetWordCertificate

def facts (n : Nat) : FactData (Fin 3) :=
  let c := factCode n
  ⟨c % 65536, certWord (c / 65536 % 256), c / 16777216⟩

end Lyons.Gebhardt.ParabolicIndexCertificate
