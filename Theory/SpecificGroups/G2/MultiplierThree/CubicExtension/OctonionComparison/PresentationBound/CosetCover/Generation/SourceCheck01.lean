module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.Relators

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem source_checked_128 : sourceChunk 128 16 = true := by decide +kernel

theorem source_checked_144 : sourceChunk 144 16 = true := by decide +kernel

theorem source_checked_160 : sourceChunk 160 16 = true := by decide +kernel

theorem source_checked_176 : sourceChunk 176 16 = true := by decide +kernel

theorem source_checked_192 : sourceChunk 192 16 = true := by decide +kernel

theorem source_checked_208 : sourceChunk 208 16 = true := by decide +kernel

theorem source_checked_224 : sourceChunk 224 16 = true := by decide +kernel

theorem source_checked_240 : sourceChunk 240 16 = true := by decide +kernel

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
