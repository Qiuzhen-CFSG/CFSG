module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.Relators

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem source_checked_384 : sourceChunk 384 16 = true := by decide +kernel

theorem source_checked_400 : sourceChunk 400 16 = true := by decide +kernel

theorem source_checked_416 : sourceChunk 416 16 = true := by decide +kernel

theorem source_checked_432 : sourceChunk 432 16 = true := by decide +kernel

theorem source_checked_448 : sourceChunk 448 16 = true := by decide +kernel

theorem source_checked_464 : sourceChunk 464 16 = true := by decide +kernel

theorem source_checked_480 : sourceChunk 480 16 = true := by decide +kernel

theorem source_checked_496 : sourceChunk 496 16 = true := by decide +kernel

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
