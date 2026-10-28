module

public import Theory.SpecificGroups.Lyons.GebhardtParabolicIndexCertificate.opCodeData00
public import Theory.SpecificGroups.Lyons.GebhardtParabolicIndexCertificate.opCodeData01
public import Theory.SpecificGroups.Lyons.GebhardtParabolicIndexCertificate.opCodeData02
public import Theory.SpecificGroups.Lyons.GebhardtParabolicIndexCertificate.opCodeData03

/-! Kernel-checked certificate data for Gebhardt (2000), Section 3B.
Reproduce with `Theory/SpecificGroups/Lyons/GebhardtParabolicIndexCertificate/source/generate.py`. -/

@[expose] public section
namespace Lyons.Gebhardt.ParabolicIndexCertificate
open Subgroup.CosetWordCertificate

def opCode (i : Nat) : Nat :=
  unpack (lookupBranch 960 (lookupBranch 480 (lookupBranch 224 (lookupBranch 96 (lookupBranch 32 opCodePage0 (lookupBranch 64 opCodePage32 opCodePage64)) (lookupBranch 160 (lookupBranch 128 opCodePage96 opCodePage128) (lookupBranch 192 opCodePage160 opCodePage192))) (lookupBranch 352 (lookupBranch 288 (lookupBranch 256 opCodePage224 opCodePage256) (lookupBranch 320 opCodePage288 opCodePage320)) (lookupBranch 416 (lookupBranch 384 opCodePage352 opCodePage384) (lookupBranch 448 opCodePage416 opCodePage448)))) (lookupBranch 704 (lookupBranch 576 (lookupBranch 512 opCodePage480 (lookupBranch 544 opCodePage512 opCodePage544)) (lookupBranch 640 (lookupBranch 608 opCodePage576 opCodePage608) (lookupBranch 672 opCodePage640 opCodePage672))) (lookupBranch 832 (lookupBranch 768 (lookupBranch 736 opCodePage704 opCodePage736) (lookupBranch 800 opCodePage768 opCodePage800)) (lookupBranch 896 (lookupBranch 864 opCodePage832 opCodePage864) (lookupBranch 928 opCodePage896 opCodePage928))))) (lookupBranch 1440 (lookupBranch 1184 (lookupBranch 1056 (lookupBranch 992 opCodePage960 (lookupBranch 1024 opCodePage992 opCodePage1024)) (lookupBranch 1120 (lookupBranch 1088 opCodePage1056 opCodePage1088) (lookupBranch 1152 opCodePage1120 opCodePage1152))) (lookupBranch 1312 (lookupBranch 1248 (lookupBranch 1216 opCodePage1184 opCodePage1216) (lookupBranch 1280 opCodePage1248 opCodePage1280)) (lookupBranch 1376 (lookupBranch 1344 opCodePage1312 opCodePage1344) (lookupBranch 1408 opCodePage1376 opCodePage1408)))) (lookupBranch 1696 (lookupBranch 1568 (lookupBranch 1504 (lookupBranch 1472 opCodePage1440 opCodePage1472) (lookupBranch 1536 opCodePage1504 opCodePage1536)) (lookupBranch 1632 (lookupBranch 1600 opCodePage1568 opCodePage1600) (lookupBranch 1664 opCodePage1632 opCodePage1664))) (lookupBranch 1824 (lookupBranch 1760 (lookupBranch 1728 opCodePage1696 opCodePage1728) (lookupBranch 1792 opCodePage1760 opCodePage1792)) (lookupBranch 1888 (lookupBranch 1856 opCodePage1824 opCodePage1856) (lookupBranch 1920 opCodePage1888 opCodePage1920)))))) 39 i

end Lyons.Gebhardt.ParabolicIndexCertificate
