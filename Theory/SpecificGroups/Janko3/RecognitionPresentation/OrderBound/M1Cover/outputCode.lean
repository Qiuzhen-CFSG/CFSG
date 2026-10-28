module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.outputCodeData00

/-! Kernel-checked coset certificate for ATLAS J3G1-P1, literal subgroup M₁.
Generated from `source/compact.json` by `source/generate.py`.
The data are untrusted; `Scan.chunk_sound` supplies actual subgroup witnesses. -/

@[expose] public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
open Subgroup.CosetWordCertificate

def outputCode (i : Nat) : Nat :=
  unpack (branch 96 (branch 32 outputCodePage0 (branch 64 outputCodePage32 outputCodePage64)) (branch 160 (branch 128 outputCodePage96 outputCodePage128) (branch 192 outputCodePage160 outputCodePage192))) 19 i

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
