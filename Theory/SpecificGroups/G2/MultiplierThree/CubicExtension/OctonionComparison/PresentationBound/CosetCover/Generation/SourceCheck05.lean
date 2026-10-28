module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.Relators

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem source_checked_640 : sourceChunk 640 16 = true := by decide +kernel

theorem source_checked_656 : sourceChunk 656 16 = true := by decide +kernel

theorem source_checked_672 : sourceChunk 672 16 = true := by decide +kernel

theorem source_checked_688 : sourceChunk 688 16 = true := by decide +kernel

theorem source_checked_704 : sourceChunk 704 16 = true := by decide +kernel

theorem source_checked_720 : sourceChunk 720 16 = true := by decide +kernel

theorem source_checked_736 : sourceChunk 736 16 = true := by decide +kernel

theorem source_checked_752 : sourceChunk 752 16 = true := by decide +kernel

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
