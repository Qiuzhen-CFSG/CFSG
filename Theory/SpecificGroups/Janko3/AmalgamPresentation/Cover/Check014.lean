module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_114688 : Path.checkChunk context decode facts instructions 114688 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_115200 : Path.checkChunk context decode facts instructions 115200 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_115712 : Path.checkChunk context decode facts instructions 115712 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_116224 : Path.checkChunk context decode facts instructions 116224 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_116736 : Path.checkChunk context decode facts instructions 116736 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_117248 : Path.checkChunk context decode facts instructions 117248 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_117760 : Path.checkChunk context decode facts instructions 117760 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_118272 : Path.checkChunk context decode facts instructions 118272 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_118784 : Path.checkChunk context decode facts instructions 118784 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_119296 : Path.checkChunk context decode facts instructions 119296 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_119808 : Path.checkChunk context decode facts instructions 119808 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_120320 : Path.checkChunk context decode facts instructions 120320 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_120832 : Path.checkChunk context decode facts instructions 120832 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_121344 : Path.checkChunk context decode facts instructions 121344 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_121856 : Path.checkChunk context decode facts instructions 121856 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_122368 : Path.checkChunk context decode facts instructions 122368 512 = true := by
  decide +kernel

theorem sound_114688 (prior : ∀ n, n < 114688 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 122880 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h115200 := Path.chunk_sound context_valid decode facts instructions 114688 512
    prior checked_114688
  have h115712 := Path.chunk_sound context_valid decode facts instructions 115200 512
    h115200 checked_115200
  have h116224 := Path.chunk_sound context_valid decode facts instructions 115712 512
    h115712 checked_115712
  have h116736 := Path.chunk_sound context_valid decode facts instructions 116224 512
    h116224 checked_116224
  have h117248 := Path.chunk_sound context_valid decode facts instructions 116736 512
    h116736 checked_116736
  have h117760 := Path.chunk_sound context_valid decode facts instructions 117248 512
    h117248 checked_117248
  have h118272 := Path.chunk_sound context_valid decode facts instructions 117760 512
    h117760 checked_117760
  have h118784 := Path.chunk_sound context_valid decode facts instructions 118272 512
    h118272 checked_118272
  have h119296 := Path.chunk_sound context_valid decode facts instructions 118784 512
    h118784 checked_118784
  have h119808 := Path.chunk_sound context_valid decode facts instructions 119296 512
    h119296 checked_119296
  have h120320 := Path.chunk_sound context_valid decode facts instructions 119808 512
    h119808 checked_119808
  have h120832 := Path.chunk_sound context_valid decode facts instructions 120320 512
    h120320 checked_120320
  have h121344 := Path.chunk_sound context_valid decode facts instructions 120832 512
    h120832 checked_120832
  have h121856 := Path.chunk_sound context_valid decode facts instructions 121344 512
    h121344 checked_121344
  have h122368 := Path.chunk_sound context_valid decode facts instructions 121856 512
    h121856 checked_121856
  have h122880 := Path.chunk_sound context_valid decode facts instructions 122368 512
    h122368 checked_122368
  exact h122880

end Sporadic.Janko3.AmalgamPresentation.Cover
