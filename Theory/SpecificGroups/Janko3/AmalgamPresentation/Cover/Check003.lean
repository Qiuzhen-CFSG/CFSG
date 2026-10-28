module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_24576 : Path.checkChunk context decode facts instructions 24576 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_25088 : Path.checkChunk context decode facts instructions 25088 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_25600 : Path.checkChunk context decode facts instructions 25600 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_26112 : Path.checkChunk context decode facts instructions 26112 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_26624 : Path.checkChunk context decode facts instructions 26624 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_27136 : Path.checkChunk context decode facts instructions 27136 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_27648 : Path.checkChunk context decode facts instructions 27648 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_28160 : Path.checkChunk context decode facts instructions 28160 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_28672 : Path.checkChunk context decode facts instructions 28672 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_29184 : Path.checkChunk context decode facts instructions 29184 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_29696 : Path.checkChunk context decode facts instructions 29696 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_30208 : Path.checkChunk context decode facts instructions 30208 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_30720 : Path.checkChunk context decode facts instructions 30720 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_31232 : Path.checkChunk context decode facts instructions 31232 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_31744 : Path.checkChunk context decode facts instructions 31744 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_32256 : Path.checkChunk context decode facts instructions 32256 512 = true := by
  decide +kernel

theorem sound_24576 (prior : ∀ n, n < 24576 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 32768 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h25088 := Path.chunk_sound context_valid decode facts instructions 24576 512
    prior checked_24576
  have h25600 := Path.chunk_sound context_valid decode facts instructions 25088 512
    h25088 checked_25088
  have h26112 := Path.chunk_sound context_valid decode facts instructions 25600 512
    h25600 checked_25600
  have h26624 := Path.chunk_sound context_valid decode facts instructions 26112 512
    h26112 checked_26112
  have h27136 := Path.chunk_sound context_valid decode facts instructions 26624 512
    h26624 checked_26624
  have h27648 := Path.chunk_sound context_valid decode facts instructions 27136 512
    h27136 checked_27136
  have h28160 := Path.chunk_sound context_valid decode facts instructions 27648 512
    h27648 checked_27648
  have h28672 := Path.chunk_sound context_valid decode facts instructions 28160 512
    h28160 checked_28160
  have h29184 := Path.chunk_sound context_valid decode facts instructions 28672 512
    h28672 checked_28672
  have h29696 := Path.chunk_sound context_valid decode facts instructions 29184 512
    h29184 checked_29184
  have h30208 := Path.chunk_sound context_valid decode facts instructions 29696 512
    h29696 checked_29696
  have h30720 := Path.chunk_sound context_valid decode facts instructions 30208 512
    h30208 checked_30208
  have h31232 := Path.chunk_sound context_valid decode facts instructions 30720 512
    h30720 checked_30720
  have h31744 := Path.chunk_sound context_valid decode facts instructions 31232 512
    h31232 checked_31232
  have h32256 := Path.chunk_sound context_valid decode facts instructions 31744 512
    h31744 checked_31744
  have h32768 := Path.chunk_sound context_valid decode facts instructions 32256 512
    h32256 checked_32256
  exact h32768

end Sporadic.Janko3.AmalgamPresentation.Cover
