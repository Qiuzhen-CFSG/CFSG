module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_0 : Path.checkChunk context decode facts instructions 0 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_512 : Path.checkChunk context decode facts instructions 512 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1024 : Path.checkChunk context decode facts instructions 1024 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1536 : Path.checkChunk context decode facts instructions 1536 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_2048 : Path.checkChunk context decode facts instructions 2048 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_2560 : Path.checkChunk context decode facts instructions 2560 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_3072 : Path.checkChunk context decode facts instructions 3072 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_3584 : Path.checkChunk context decode facts instructions 3584 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_4096 : Path.checkChunk context decode facts instructions 4096 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_4608 : Path.checkChunk context decode facts instructions 4608 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_5120 : Path.checkChunk context decode facts instructions 5120 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_5632 : Path.checkChunk context decode facts instructions 5632 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_6144 : Path.checkChunk context decode facts instructions 6144 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_6656 : Path.checkChunk context decode facts instructions 6656 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_7168 : Path.checkChunk context decode facts instructions 7168 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_7680 : Path.checkChunk context decode facts instructions 7680 512 = true := by
  decide +kernel

theorem sound_0 (prior : ∀ n, n < 0 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 8192 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h512 := Path.chunk_sound context_valid decode facts instructions 0 512
    prior checked_0
  have h1024 := Path.chunk_sound context_valid decode facts instructions 512 512
    h512 checked_512
  have h1536 := Path.chunk_sound context_valid decode facts instructions 1024 512
    h1024 checked_1024
  have h2048 := Path.chunk_sound context_valid decode facts instructions 1536 512
    h1536 checked_1536
  have h2560 := Path.chunk_sound context_valid decode facts instructions 2048 512
    h2048 checked_2048
  have h3072 := Path.chunk_sound context_valid decode facts instructions 2560 512
    h2560 checked_2560
  have h3584 := Path.chunk_sound context_valid decode facts instructions 3072 512
    h3072 checked_3072
  have h4096 := Path.chunk_sound context_valid decode facts instructions 3584 512
    h3584 checked_3584
  have h4608 := Path.chunk_sound context_valid decode facts instructions 4096 512
    h4096 checked_4096
  have h5120 := Path.chunk_sound context_valid decode facts instructions 4608 512
    h4608 checked_4608
  have h5632 := Path.chunk_sound context_valid decode facts instructions 5120 512
    h5120 checked_5120
  have h6144 := Path.chunk_sound context_valid decode facts instructions 5632 512
    h5632 checked_5632
  have h6656 := Path.chunk_sound context_valid decode facts instructions 6144 512
    h6144 checked_6144
  have h7168 := Path.chunk_sound context_valid decode facts instructions 6656 512
    h6656 checked_6656
  have h7680 := Path.chunk_sound context_valid decode facts instructions 7168 512
    h7168 checked_7168
  have h8192 := Path.chunk_sound context_valid decode facts instructions 7680 512
    h7680 checked_7680
  exact h8192

end Sporadic.Janko3.AmalgamPresentation.Cover
