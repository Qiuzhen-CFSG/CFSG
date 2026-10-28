module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.OutputBase
public import Mathlib.Tactic.IntervalCases

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem output_checked_0 : outputChunk 0 16 = true := by decide +kernel

theorem output_checked_16 : outputChunk 16 16 = true := by decide +kernel

theorem output_checked_32 : outputChunk 32 16 = true := by decide +kernel

theorem output_checked_48 : outputChunk 48 16 = true := by decide +kernel

theorem output_checked_64 : outputChunk 64 16 = true := by decide +kernel

theorem output_checked_80 : outputChunk 80 16 = true := by decide +kernel

theorem output_checked_96 : outputChunk 96 16 = true := by decide +kernel

theorem output_checked_112 : outputChunk 112 16 = true := by decide +kernel

theorem output_checked_128 : outputChunk 128 16 = true := by decide +kernel

theorem output_checked_144 : outputChunk 144 16 = true := by decide +kernel

theorem output_checked_160 : outputChunk 160 16 = true := by decide +kernel

theorem output_checked_176 : outputChunk 176 16 = true := by decide +kernel

theorem output_checked_192 : outputChunk 192 16 = true := by decide +kernel

theorem output_checked_208 : outputChunk 208 16 = true := by decide +kernel

theorem output_checked_224 : outputChunk 224 16 = true := by decide +kernel

theorem output_checked_240 : outputChunk 240 16 = true := by decide +kernel

theorem output_checked_256 : outputChunk 256 16 = true := by decide +kernel

theorem output_checked_272 : outputChunk 272 16 = true := by decide +kernel

theorem output_checked_288 : outputChunk 288 16 = true := by decide +kernel

theorem output_checked_304 : outputChunk 304 16 = true := by decide +kernel

theorem output_checked_320 : outputChunk 320 16 = true := by decide +kernel

theorem output_checked_336 : outputChunk 336 16 = true := by decide +kernel

theorem output_checked_352 : outputChunk 352 15 = true := by decide +kernel

theorem output_spec (k : Label) :
    Scan.pathCheck facts 76703 0 (outputs k.val) 0 = true ∧
      reduce (Scan.pathWord facts (outputs k.val)) = [(k, true)] := by
  have hb : k.val / 16 < 23 := by omega
  interval_cases hc : k.val / 16

  · exact outputChunk_spec 0 16 output_checked_0 k (by omega) (by omega)

  · exact outputChunk_spec 16 16 output_checked_16 k (by omega) (by omega)

  · exact outputChunk_spec 32 16 output_checked_32 k (by omega) (by omega)

  · exact outputChunk_spec 48 16 output_checked_48 k (by omega) (by omega)

  · exact outputChunk_spec 64 16 output_checked_64 k (by omega) (by omega)

  · exact outputChunk_spec 80 16 output_checked_80 k (by omega) (by omega)

  · exact outputChunk_spec 96 16 output_checked_96 k (by omega) (by omega)

  · exact outputChunk_spec 112 16 output_checked_112 k (by omega) (by omega)

  · exact outputChunk_spec 128 16 output_checked_128 k (by omega) (by omega)

  · exact outputChunk_spec 144 16 output_checked_144 k (by omega) (by omega)

  · exact outputChunk_spec 160 16 output_checked_160 k (by omega) (by omega)

  · exact outputChunk_spec 176 16 output_checked_176 k (by omega) (by omega)

  · exact outputChunk_spec 192 16 output_checked_192 k (by omega) (by omega)

  · exact outputChunk_spec 208 16 output_checked_208 k (by omega) (by omega)

  · exact outputChunk_spec 224 16 output_checked_224 k (by omega) (by omega)

  · exact outputChunk_spec 240 16 output_checked_240 k (by omega) (by omega)

  · exact outputChunk_spec 256 16 output_checked_256 k (by omega) (by omega)

  · exact outputChunk_spec 272 16 output_checked_272 k (by omega) (by omega)

  · exact outputChunk_spec 288 16 output_checked_288 k (by omega) (by omega)

  · exact outputChunk_spec 304 16 output_checked_304 k (by omega) (by omega)

  · exact outputChunk_spec 320 16 output_checked_320 k (by omega) (by omega)

  · exact outputChunk_spec 336 16 output_checked_336 k (by omega) (by omega)

  · exact outputChunk_spec 352 15 output_checked_352 k (by omega) (by omega)

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
