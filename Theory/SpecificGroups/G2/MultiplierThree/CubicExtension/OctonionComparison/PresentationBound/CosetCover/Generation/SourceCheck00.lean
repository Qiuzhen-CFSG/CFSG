module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.Relators

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem source_checked_0 : sourceChunk 0 16 = true := by decide +kernel

theorem source_checked_16 : sourceChunk 16 16 = true := by decide +kernel

theorem source_checked_32 : sourceChunk 32 16 = true := by decide +kernel

theorem source_checked_48 : sourceChunk 48 16 = true := by decide +kernel

theorem source_checked_64 : sourceChunk 64 16 = true := by decide +kernel

theorem source_checked_80 : sourceChunk 80 16 = true := by decide +kernel

theorem source_checked_96 : sourceChunk 96 16 = true := by decide +kernel

theorem source_checked_112 : sourceChunk 112 16 = true := by decide +kernel

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
