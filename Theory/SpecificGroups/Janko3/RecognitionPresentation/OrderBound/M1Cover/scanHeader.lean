module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.scanHeaderData00

/-! Kernel-checked coset certificate for ATLAS J3G1-P1, literal subgroup M₁.
Generated from `source/compact.json` by `source/generate.py`.
The data are untrusted; `Scan.chunk_sound` supplies actual subgroup witnesses. -/

@[expose] public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
open Subgroup.CosetWordCertificate

def scanHeader (i : Nat) : Nat :=
  unpack (branch 128 (branch 64 (branch 32 scanHeaderPage0 scanHeaderPage32) (branch 96 scanHeaderPage64 scanHeaderPage96)) (branch 192 (branch 160 scanHeaderPage128 scanHeaderPage160) (branch 224 scanHeaderPage192 (branch 256 scanHeaderPage224 scanHeaderPage256)))) 29 i

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
