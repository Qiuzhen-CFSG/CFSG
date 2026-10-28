module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.Relators

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem source_checked_2560 : sourceChunk 2560 16 = true := by decide +kernel

theorem source_checked_2576 : sourceChunk 2576 16 = true := by decide +kernel

theorem source_checked_2592 : sourceChunk 2592 16 = true := by decide +kernel

theorem source_checked_2608 : sourceChunk 2608 16 = true := by decide +kernel

theorem source_checked_2624 : sourceChunk 2624 16 = true := by decide +kernel

theorem source_checked_2640 : sourceChunk 2640 16 = true := by decide +kernel

theorem source_checked_2656 : sourceChunk 2656 16 = true := by decide +kernel

theorem source_checked_2672 : sourceChunk 2672 16 = true := by decide +kernel

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
