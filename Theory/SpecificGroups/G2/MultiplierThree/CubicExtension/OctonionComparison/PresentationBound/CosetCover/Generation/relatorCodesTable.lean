module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.relatorCodesData00
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.relatorCodesData01
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.relatorCodesData02
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.relatorCodesData03

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

@[expose] public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

def relatorCodes : Nat → Nat :=
  (lookup 1536 (lookup 768 (lookup 384 (lookup 128 relatorCodes0 (lookup 256 relatorCodes128 relatorCodes256)) (lookup 512 relatorCodes384 (lookup 640 relatorCodes512 relatorCodes640))) (lookup 1152 (lookup 896 relatorCodes768 (lookup 1024 relatorCodes896 relatorCodes1024)) (lookup 1280 relatorCodes1152 (lookup 1408 relatorCodes1280 relatorCodes1408)))) (lookup 2304 (lookup 1920 (lookup 1664 relatorCodes1536 (lookup 1792 relatorCodes1664 relatorCodes1792)) (lookup 2048 relatorCodes1920 (lookup 2176 relatorCodes2048 relatorCodes2176))) (lookup 2688 (lookup 2432 relatorCodes2304 (lookup 2560 relatorCodes2432 relatorCodes2560)) (lookup 2944 (lookup 2816 relatorCodes2688 relatorCodes2816) (lookup 3072 relatorCodes2944 relatorCodes3072)))))

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
