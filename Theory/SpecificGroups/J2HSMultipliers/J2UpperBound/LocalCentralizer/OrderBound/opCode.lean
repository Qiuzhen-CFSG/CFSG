module

public import Theory.SpecificGroups.J2HSMultipliers.J2UpperBound.LocalCentralizer.OrderBound.opCodeData00

/-! Kernel-checked coset certificate for the normalized J₂ centralizer presentation, the trivial subgroup.
Generated from `source/compact.json` by `source/generate.py`.
The data are untrusted; `Scan.chunk_sound` supplies actual subgroup witnesses. -/

@[expose] public section
namespace Theory.SpecificGroups.J2HSMultipliers.J2.LocalCentralizerPresentation.OrderBound
open Subgroup.CosetWordCertificate

def opCode (i : Nat) : Nat :=
  unpack (branch 160 (branch 64 (branch 32 opCodePage0 opCodePage32) (branch 96 opCodePage64 (branch 128 opCodePage96 opCodePage128))) (branch 256 (branch 192 opCodePage160 (branch 224 opCodePage192 opCodePage224)) (branch 288 opCodePage256 (branch 320 opCodePage288 opCodePage320)))) 37 i

end Theory.SpecificGroups.J2HSMultipliers.J2.LocalCentralizerPresentation.OrderBound
