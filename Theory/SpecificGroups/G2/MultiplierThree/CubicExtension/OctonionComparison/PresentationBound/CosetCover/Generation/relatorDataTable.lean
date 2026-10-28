module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.relatorDataData00
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.relatorDataData01
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.relatorDataData02
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.relatorDataData03

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

@[expose] public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

def relatorData : Nat → Word Label :=
  (lookup 1536 (lookup 768 (lookup 384 (lookup 128 relatorData0 (lookup 256 relatorData128 relatorData256)) (lookup 512 relatorData384 (lookup 640 relatorData512 relatorData640))) (lookup 1152 (lookup 896 relatorData768 (lookup 1024 relatorData896 relatorData1024)) (lookup 1280 relatorData1152 (lookup 1408 relatorData1280 relatorData1408)))) (lookup 2304 (lookup 1920 (lookup 1664 relatorData1536 (lookup 1792 relatorData1664 relatorData1792)) (lookup 2048 relatorData1920 (lookup 2176 relatorData2048 relatorData2176))) (lookup 2688 (lookup 2432 relatorData2304 (lookup 2560 relatorData2432 relatorData2560)) (lookup 2944 (lookup 2816 relatorData2688 relatorData2816) (lookup 3072 relatorData2944 relatorData3072)))))

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
