module

public import Theory.SpecificGroups.J2HSMultipliers.J2UpperBound.LocalCentralizer.OrderBound.factCodeData00

/-! Kernel-checked coset certificate for the normalized J₂ centralizer presentation, the trivial subgroup.
Generated from `source/compact.json` by `source/generate.py`.
The data are untrusted; `Scan.chunk_sound` supplies actual subgroup witnesses. -/

@[expose] public section
namespace Theory.SpecificGroups.J2HSMultipliers.J2.LocalCentralizerPresentation.OrderBound
open Subgroup.CosetWordCertificate

def factCode (i : Nat) : Nat :=
  unpack (branch 160 (branch 64 (branch 32 factCodePage0 factCodePage32) (branch 96 factCodePage64 (branch 128 factCodePage96 factCodePage128))) (branch 256 (branch 192 factCodePage160 (branch 224 factCodePage192 factCodePage224)) (branch 288 factCodePage256 (branch 320 factCodePage288 factCodePage320)))) 31 i

end Theory.SpecificGroups.J2HSMultipliers.J2.LocalCentralizerPresentation.OrderBound
