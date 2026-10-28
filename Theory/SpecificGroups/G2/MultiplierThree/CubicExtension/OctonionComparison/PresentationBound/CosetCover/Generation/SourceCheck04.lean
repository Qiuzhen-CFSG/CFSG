module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.Relators

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem source_checked_512 : sourceChunk 512 16 = true := by decide +kernel

theorem source_checked_528 : sourceChunk 528 16 = true := by decide +kernel

theorem source_checked_544 : sourceChunk 544 16 = true := by decide +kernel

theorem source_checked_560 : sourceChunk 560 16 = true := by decide +kernel

theorem source_checked_576 : sourceChunk 576 16 = true := by decide +kernel

theorem source_checked_592 : sourceChunk 592 16 = true := by decide +kernel

theorem source_checked_608 : sourceChunk 608 16 = true := by decide +kernel

theorem source_checked_624 : sourceChunk 624 16 = true := by decide +kernel

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
