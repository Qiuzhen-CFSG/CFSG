module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1048576 : Path.checkChunk context decode facts instructions 1048576 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1049088 : Path.checkChunk context decode facts instructions 1049088 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1049600 : Path.checkChunk context decode facts instructions 1049600 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1050112 : Path.checkChunk context decode facts instructions 1050112 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1050624 : Path.checkChunk context decode facts instructions 1050624 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1051136 : Path.checkChunk context decode facts instructions 1051136 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1051648 : Path.checkChunk context decode facts instructions 1051648 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1052160 : Path.checkChunk context decode facts instructions 1052160 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1052672 : Path.checkChunk context decode facts instructions 1052672 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1053184 : Path.checkChunk context decode facts instructions 1053184 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1053696 : Path.checkChunk context decode facts instructions 1053696 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1054208 : Path.checkChunk context decode facts instructions 1054208 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1054720 : Path.checkChunk context decode facts instructions 1054720 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1055232 : Path.checkChunk context decode facts instructions 1055232 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1055744 : Path.checkChunk context decode facts instructions 1055744 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1056256 : Path.checkChunk context decode facts instructions 1056256 512 = true := by
  decide +kernel

theorem sound_1048576 (prior : ∀ n, n < 1048576 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1056768 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1049088 := Path.chunk_sound context_valid decode facts instructions 1048576 512
    prior checked_1048576
  have h1049600 := Path.chunk_sound context_valid decode facts instructions 1049088 512
    h1049088 checked_1049088
  have h1050112 := Path.chunk_sound context_valid decode facts instructions 1049600 512
    h1049600 checked_1049600
  have h1050624 := Path.chunk_sound context_valid decode facts instructions 1050112 512
    h1050112 checked_1050112
  have h1051136 := Path.chunk_sound context_valid decode facts instructions 1050624 512
    h1050624 checked_1050624
  have h1051648 := Path.chunk_sound context_valid decode facts instructions 1051136 512
    h1051136 checked_1051136
  have h1052160 := Path.chunk_sound context_valid decode facts instructions 1051648 512
    h1051648 checked_1051648
  have h1052672 := Path.chunk_sound context_valid decode facts instructions 1052160 512
    h1052160 checked_1052160
  have h1053184 := Path.chunk_sound context_valid decode facts instructions 1052672 512
    h1052672 checked_1052672
  have h1053696 := Path.chunk_sound context_valid decode facts instructions 1053184 512
    h1053184 checked_1053184
  have h1054208 := Path.chunk_sound context_valid decode facts instructions 1053696 512
    h1053696 checked_1053696
  have h1054720 := Path.chunk_sound context_valid decode facts instructions 1054208 512
    h1054208 checked_1054208
  have h1055232 := Path.chunk_sound context_valid decode facts instructions 1054720 512
    h1054720 checked_1054720
  have h1055744 := Path.chunk_sound context_valid decode facts instructions 1055232 512
    h1055232 checked_1055232
  have h1056256 := Path.chunk_sound context_valid decode facts instructions 1055744 512
    h1055744 checked_1055744
  have h1056768 := Path.chunk_sound context_valid decode facts instructions 1056256 512
    h1056256 checked_1056256
  exact h1056768

end Sporadic.Janko3.AmalgamPresentation.Cover
