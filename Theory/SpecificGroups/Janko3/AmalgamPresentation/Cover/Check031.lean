module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_253952 : Path.checkChunk context decode facts instructions 253952 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_254464 : Path.checkChunk context decode facts instructions 254464 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_254976 : Path.checkChunk context decode facts instructions 254976 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_255488 : Path.checkChunk context decode facts instructions 255488 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_256000 : Path.checkChunk context decode facts instructions 256000 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_256512 : Path.checkChunk context decode facts instructions 256512 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_257024 : Path.checkChunk context decode facts instructions 257024 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_257536 : Path.checkChunk context decode facts instructions 257536 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_258048 : Path.checkChunk context decode facts instructions 258048 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_258560 : Path.checkChunk context decode facts instructions 258560 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_259072 : Path.checkChunk context decode facts instructions 259072 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_259584 : Path.checkChunk context decode facts instructions 259584 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_260096 : Path.checkChunk context decode facts instructions 260096 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_260608 : Path.checkChunk context decode facts instructions 260608 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_261120 : Path.checkChunk context decode facts instructions 261120 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_261632 : Path.checkChunk context decode facts instructions 261632 512 = true := by
  decide +kernel

theorem sound_253952 (prior : ∀ n, n < 253952 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 262144 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h254464 := Path.chunk_sound context_valid decode facts instructions 253952 512
    prior checked_253952
  have h254976 := Path.chunk_sound context_valid decode facts instructions 254464 512
    h254464 checked_254464
  have h255488 := Path.chunk_sound context_valid decode facts instructions 254976 512
    h254976 checked_254976
  have h256000 := Path.chunk_sound context_valid decode facts instructions 255488 512
    h255488 checked_255488
  have h256512 := Path.chunk_sound context_valid decode facts instructions 256000 512
    h256000 checked_256000
  have h257024 := Path.chunk_sound context_valid decode facts instructions 256512 512
    h256512 checked_256512
  have h257536 := Path.chunk_sound context_valid decode facts instructions 257024 512
    h257024 checked_257024
  have h258048 := Path.chunk_sound context_valid decode facts instructions 257536 512
    h257536 checked_257536
  have h258560 := Path.chunk_sound context_valid decode facts instructions 258048 512
    h258048 checked_258048
  have h259072 := Path.chunk_sound context_valid decode facts instructions 258560 512
    h258560 checked_258560
  have h259584 := Path.chunk_sound context_valid decode facts instructions 259072 512
    h259072 checked_259072
  have h260096 := Path.chunk_sound context_valid decode facts instructions 259584 512
    h259584 checked_259584
  have h260608 := Path.chunk_sound context_valid decode facts instructions 260096 512
    h260096 checked_260096
  have h261120 := Path.chunk_sound context_valid decode facts instructions 260608 512
    h260608 checked_260608
  have h261632 := Path.chunk_sound context_valid decode facts instructions 261120 512
    h261120 checked_261120
  have h262144 := Path.chunk_sound context_valid decode facts instructions 261632 512
    h261632 checked_261632
  exact h262144

end Sporadic.Janko3.AmalgamPresentation.Cover
