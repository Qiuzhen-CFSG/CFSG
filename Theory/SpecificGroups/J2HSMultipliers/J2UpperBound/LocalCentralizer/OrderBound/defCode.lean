module

public import Theory.SpecificGroups.J2HSMultipliers.J2UpperBound.LocalCentralizer.OrderBound.defCodeData00

/-! Kernel-checked coset certificate for the normalized J₂ centralizer presentation, the trivial subgroup.
Generated from `source/compact.json` by `source/generate.py`.
The data are untrusted; `Scan.chunk_sound` supplies actual subgroup witnesses. -/

@[expose] public section
namespace Theory.SpecificGroups.J2HSMultipliers.J2.LocalCentralizerPresentation.OrderBound
open Subgroup.CosetWordCertificate

def defCode (i : Nat) : Nat :=
  unpack (branch 64 (branch 32 defCodePage0 defCodePage32) (branch 96 defCodePage64 defCodePage96)) 16 i

end Theory.SpecificGroups.J2HSMultipliers.J2.LocalCentralizerPresentation.OrderBound
