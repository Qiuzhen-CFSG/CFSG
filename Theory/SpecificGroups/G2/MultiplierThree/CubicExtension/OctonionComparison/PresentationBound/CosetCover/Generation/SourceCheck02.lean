module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.Relators

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem source_checked_256 : sourceChunk 256 16 = true := by decide +kernel

theorem source_checked_272 : sourceChunk 272 16 = true := by decide +kernel

theorem source_checked_288 : sourceChunk 288 16 = true := by decide +kernel

theorem source_checked_304 : sourceChunk 304 16 = true := by decide +kernel

theorem source_checked_320 : sourceChunk 320 16 = true := by decide +kernel

theorem source_checked_336 : sourceChunk 336 16 = true := by decide +kernel

theorem source_checked_352 : sourceChunk 352 16 = true := by decide +kernel

theorem source_checked_368 : sourceChunk 368 16 = true := by decide +kernel

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
