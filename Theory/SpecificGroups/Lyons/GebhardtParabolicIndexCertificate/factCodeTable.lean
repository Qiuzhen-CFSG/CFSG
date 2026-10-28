module

public import Theory.SpecificGroups.Lyons.GebhardtParabolicIndexCertificate.factCodeData00
public import Theory.SpecificGroups.Lyons.GebhardtParabolicIndexCertificate.factCodeData01
public import Theory.SpecificGroups.Lyons.GebhardtParabolicIndexCertificate.factCodeData02
public import Theory.SpecificGroups.Lyons.GebhardtParabolicIndexCertificate.factCodeData03

/-! Kernel-checked certificate data for Gebhardt (2000), Section 3B.
Reproduce with `Theory/SpecificGroups/Lyons/GebhardtParabolicIndexCertificate/source/generate.py`. -/

@[expose] public section
namespace Lyons.Gebhardt.ParabolicIndexCertificate
open Subgroup.CosetWordCertificate

def factCode (i : Nat) : Nat :=
  unpack (lookupBranch 960 (lookupBranch 480 (lookupBranch 224 (lookupBranch 96 (lookupBranch 32 factCodePage0 (lookupBranch 64 factCodePage32 factCodePage64)) (lookupBranch 160 (lookupBranch 128 factCodePage96 factCodePage128) (lookupBranch 192 factCodePage160 factCodePage192))) (lookupBranch 352 (lookupBranch 288 (lookupBranch 256 factCodePage224 factCodePage256) (lookupBranch 320 factCodePage288 factCodePage320)) (lookupBranch 416 (lookupBranch 384 factCodePage352 factCodePage384) (lookupBranch 448 factCodePage416 factCodePage448)))) (lookupBranch 704 (lookupBranch 576 (lookupBranch 512 factCodePage480 (lookupBranch 544 factCodePage512 factCodePage544)) (lookupBranch 640 (lookupBranch 608 factCodePage576 factCodePage608) (lookupBranch 672 factCodePage640 factCodePage672))) (lookupBranch 832 (lookupBranch 768 (lookupBranch 736 factCodePage704 factCodePage736) (lookupBranch 800 factCodePage768 factCodePage800)) (lookupBranch 896 (lookupBranch 864 factCodePage832 factCodePage864) (lookupBranch 928 factCodePage896 factCodePage928))))) (lookupBranch 1440 (lookupBranch 1184 (lookupBranch 1056 (lookupBranch 992 factCodePage960 (lookupBranch 1024 factCodePage992 factCodePage1024)) (lookupBranch 1120 (lookupBranch 1088 factCodePage1056 factCodePage1088) (lookupBranch 1152 factCodePage1120 factCodePage1152))) (lookupBranch 1312 (lookupBranch 1248 (lookupBranch 1216 factCodePage1184 factCodePage1216) (lookupBranch 1280 factCodePage1248 factCodePage1280)) (lookupBranch 1376 (lookupBranch 1344 factCodePage1312 factCodePage1344) (lookupBranch 1408 factCodePage1376 factCodePage1408)))) (lookupBranch 1696 (lookupBranch 1568 (lookupBranch 1504 (lookupBranch 1472 factCodePage1440 factCodePage1472) (lookupBranch 1536 factCodePage1504 factCodePage1536)) (lookupBranch 1632 (lookupBranch 1600 factCodePage1568 factCodePage1600) (lookupBranch 1664 factCodePage1632 factCodePage1664))) (lookupBranch 1824 (lookupBranch 1760 (lookupBranch 1728 factCodePage1696 factCodePage1728) (lookupBranch 1792 factCodePage1760 factCodePage1792)) (lookupBranch 1888 (lookupBranch 1856 factCodePage1824 factCodePage1856) (lookupBranch 1920 factCodePage1888 factCodePage1920)))))) 40 i

end Lyons.Gebhardt.ParabolicIndexCertificate
