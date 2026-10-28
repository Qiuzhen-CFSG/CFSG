module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.defCodeData00
public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.defCodeData01

/-! Kernel-checked coset certificate for ATLAS J3G1-P1, literal subgroup M₁.
Generated from `source/compact.json` by `source/generate.py`.
The data are untrusted; `Scan.chunk_sound` supplies actual subgroup witnesses. -/

@[expose] public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
open Subgroup.CosetWordCertificate

def defCode (i : Nat) : Nat :=
  unpack (branch 576 (branch 288 (branch 128 (branch 64 (branch 32 defCodePage0 defCodePage32) (branch 96 defCodePage64 defCodePage96)) (branch 192 (branch 160 defCodePage128 defCodePage160) (branch 224 defCodePage192 (branch 256 defCodePage224 defCodePage256)))) (branch 416 (branch 352 (branch 320 defCodePage288 defCodePage320) (branch 384 defCodePage352 defCodePage384)) (branch 480 (branch 448 defCodePage416 defCodePage448) (branch 512 defCodePage480 (branch 544 defCodePage512 defCodePage544))))) (branch 864 (branch 704 (branch 640 (branch 608 defCodePage576 defCodePage608) (branch 672 defCodePage640 defCodePage672)) (branch 768 (branch 736 defCodePage704 defCodePage736) (branch 800 defCodePage768 (branch 832 defCodePage800 defCodePage832)))) (branch 1024 (branch 928 (branch 896 defCodePage864 defCodePage896) (branch 960 defCodePage928 (branch 992 defCodePage960 defCodePage992))) (branch 1088 (branch 1056 defCodePage1024 defCodePage1056) (branch 1120 defCodePage1088 (branch 1152 defCodePage1120 defCodePage1152)))))) 21 i

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
