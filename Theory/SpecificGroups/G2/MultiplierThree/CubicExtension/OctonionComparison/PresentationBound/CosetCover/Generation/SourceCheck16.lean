module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.Relators

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem source_checked_2048 : sourceChunk 2048 16 = true := by decide +kernel

theorem source_checked_2064 : sourceChunk 2064 16 = true := by decide +kernel

theorem source_checked_2080 : sourceChunk 2080 16 = true := by decide +kernel

theorem source_checked_2096 : sourceChunk 2096 16 = true := by decide +kernel

theorem source_checked_2112 : sourceChunk 2112 16 = true := by decide +kernel

theorem source_checked_2128 : sourceChunk 2128 16 = true := by decide +kernel

theorem source_checked_2144 : sourceChunk 2144 16 = true := by decide +kernel

theorem source_checked_2160 : sourceChunk 2160 16 = true := by decide +kernel

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
