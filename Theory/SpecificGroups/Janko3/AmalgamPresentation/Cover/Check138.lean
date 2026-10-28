module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1130496 : Path.checkChunk context decode facts instructions 1130496 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1131008 : Path.checkChunk context decode facts instructions 1131008 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1131520 : Path.checkChunk context decode facts instructions 1131520 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1132032 : Path.checkChunk context decode facts instructions 1132032 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1132544 : Path.checkChunk context decode facts instructions 1132544 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1133056 : Path.checkChunk context decode facts instructions 1133056 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1133568 : Path.checkChunk context decode facts instructions 1133568 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1134080 : Path.checkChunk context decode facts instructions 1134080 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1134592 : Path.checkChunk context decode facts instructions 1134592 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1135104 : Path.checkChunk context decode facts instructions 1135104 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1135616 : Path.checkChunk context decode facts instructions 1135616 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1136128 : Path.checkChunk context decode facts instructions 1136128 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1136640 : Path.checkChunk context decode facts instructions 1136640 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1137152 : Path.checkChunk context decode facts instructions 1137152 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1137664 : Path.checkChunk context decode facts instructions 1137664 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1138176 : Path.checkChunk context decode facts instructions 1138176 512 = true := by
  decide +kernel

theorem sound_1130496 (prior : ∀ n, n < 1130496 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1138688 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1131008 := Path.chunk_sound context_valid decode facts instructions 1130496 512
    prior checked_1130496
  have h1131520 := Path.chunk_sound context_valid decode facts instructions 1131008 512
    h1131008 checked_1131008
  have h1132032 := Path.chunk_sound context_valid decode facts instructions 1131520 512
    h1131520 checked_1131520
  have h1132544 := Path.chunk_sound context_valid decode facts instructions 1132032 512
    h1132032 checked_1132032
  have h1133056 := Path.chunk_sound context_valid decode facts instructions 1132544 512
    h1132544 checked_1132544
  have h1133568 := Path.chunk_sound context_valid decode facts instructions 1133056 512
    h1133056 checked_1133056
  have h1134080 := Path.chunk_sound context_valid decode facts instructions 1133568 512
    h1133568 checked_1133568
  have h1134592 := Path.chunk_sound context_valid decode facts instructions 1134080 512
    h1134080 checked_1134080
  have h1135104 := Path.chunk_sound context_valid decode facts instructions 1134592 512
    h1134592 checked_1134592
  have h1135616 := Path.chunk_sound context_valid decode facts instructions 1135104 512
    h1135104 checked_1135104
  have h1136128 := Path.chunk_sound context_valid decode facts instructions 1135616 512
    h1135616 checked_1135616
  have h1136640 := Path.chunk_sound context_valid decode facts instructions 1136128 512
    h1136128 checked_1136128
  have h1137152 := Path.chunk_sound context_valid decode facts instructions 1136640 512
    h1136640 checked_1136640
  have h1137664 := Path.chunk_sound context_valid decode facts instructions 1137152 512
    h1137152 checked_1137152
  have h1138176 := Path.chunk_sound context_valid decode facts instructions 1137664 512
    h1137664 checked_1137664
  have h1138688 := Path.chunk_sound context_valid decode facts instructions 1138176 512
    h1138176 checked_1138176
  exact h1138688

end Sporadic.Janko3.AmalgamPresentation.Cover
