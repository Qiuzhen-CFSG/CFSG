module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_368640 : Path.checkChunk context decode facts instructions 368640 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_369152 : Path.checkChunk context decode facts instructions 369152 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_369664 : Path.checkChunk context decode facts instructions 369664 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_370176 : Path.checkChunk context decode facts instructions 370176 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_370688 : Path.checkChunk context decode facts instructions 370688 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_371200 : Path.checkChunk context decode facts instructions 371200 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_371712 : Path.checkChunk context decode facts instructions 371712 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_372224 : Path.checkChunk context decode facts instructions 372224 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_372736 : Path.checkChunk context decode facts instructions 372736 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_373248 : Path.checkChunk context decode facts instructions 373248 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_373760 : Path.checkChunk context decode facts instructions 373760 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_374272 : Path.checkChunk context decode facts instructions 374272 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_374784 : Path.checkChunk context decode facts instructions 374784 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_375296 : Path.checkChunk context decode facts instructions 375296 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_375808 : Path.checkChunk context decode facts instructions 375808 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_376320 : Path.checkChunk context decode facts instructions 376320 512 = true := by
  decide +kernel

theorem sound_368640 (prior : ∀ n, n < 368640 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 376832 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h369152 := Path.chunk_sound context_valid decode facts instructions 368640 512
    prior checked_368640
  have h369664 := Path.chunk_sound context_valid decode facts instructions 369152 512
    h369152 checked_369152
  have h370176 := Path.chunk_sound context_valid decode facts instructions 369664 512
    h369664 checked_369664
  have h370688 := Path.chunk_sound context_valid decode facts instructions 370176 512
    h370176 checked_370176
  have h371200 := Path.chunk_sound context_valid decode facts instructions 370688 512
    h370688 checked_370688
  have h371712 := Path.chunk_sound context_valid decode facts instructions 371200 512
    h371200 checked_371200
  have h372224 := Path.chunk_sound context_valid decode facts instructions 371712 512
    h371712 checked_371712
  have h372736 := Path.chunk_sound context_valid decode facts instructions 372224 512
    h372224 checked_372224
  have h373248 := Path.chunk_sound context_valid decode facts instructions 372736 512
    h372736 checked_372736
  have h373760 := Path.chunk_sound context_valid decode facts instructions 373248 512
    h373248 checked_373248
  have h374272 := Path.chunk_sound context_valid decode facts instructions 373760 512
    h373760 checked_373760
  have h374784 := Path.chunk_sound context_valid decode facts instructions 374272 512
    h374272 checked_374272
  have h375296 := Path.chunk_sound context_valid decode facts instructions 374784 512
    h374784 checked_374784
  have h375808 := Path.chunk_sound context_valid decode facts instructions 375296 512
    h375296 checked_375296
  have h376320 := Path.chunk_sound context_valid decode facts instructions 375808 512
    h375808 checked_375808
  have h376832 := Path.chunk_sound context_valid decode facts instructions 376320 512
    h376320 checked_376320
  exact h376832

end Sporadic.Janko3.AmalgamPresentation.Cover
