module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.Relators

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem source_checked_1024 : sourceChunk 1024 16 = true := by decide +kernel

theorem source_checked_1040 : sourceChunk 1040 16 = true := by decide +kernel

theorem source_checked_1056 : sourceChunk 1056 16 = true := by decide +kernel

theorem source_checked_1072 : sourceChunk 1072 16 = true := by decide +kernel

theorem source_checked_1088 : sourceChunk 1088 16 = true := by decide +kernel

theorem source_checked_1104 : sourceChunk 1104 16 = true := by decide +kernel

theorem source_checked_1120 : sourceChunk 1120 16 = true := by decide +kernel

theorem source_checked_1136 : sourceChunk 1136 16 = true := by decide +kernel

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
