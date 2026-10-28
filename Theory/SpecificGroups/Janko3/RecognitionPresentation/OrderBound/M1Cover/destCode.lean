module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.destCodeData00

/-! Kernel-checked coset certificate for ATLAS J3G1-P1, literal subgroup M₁.
Generated from `source/compact.json` by `source/generate.py`.
The data are untrusted; `Scan.chunk_sound` supplies actual subgroup witnesses. -/

@[expose] public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
open Subgroup.CosetWordCertificate

def destCode (i : Nat) : Nat :=
  unpack (branch 96 (branch 32 destCodePage0 (branch 64 destCodePage32 destCodePage64)) (branch 160 (branch 128 destCodePage96 destCodePage128) (branch 192 destCodePage160 destCodePage192))) 13 i

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
