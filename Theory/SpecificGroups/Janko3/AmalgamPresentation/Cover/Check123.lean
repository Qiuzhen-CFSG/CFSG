module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1007616 : Path.checkChunk context decode facts instructions 1007616 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1008128 : Path.checkChunk context decode facts instructions 1008128 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1008640 : Path.checkChunk context decode facts instructions 1008640 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1009152 : Path.checkChunk context decode facts instructions 1009152 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1009664 : Path.checkChunk context decode facts instructions 1009664 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1010176 : Path.checkChunk context decode facts instructions 1010176 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1010688 : Path.checkChunk context decode facts instructions 1010688 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1011200 : Path.checkChunk context decode facts instructions 1011200 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1011712 : Path.checkChunk context decode facts instructions 1011712 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1012224 : Path.checkChunk context decode facts instructions 1012224 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1012736 : Path.checkChunk context decode facts instructions 1012736 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1013248 : Path.checkChunk context decode facts instructions 1013248 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1013760 : Path.checkChunk context decode facts instructions 1013760 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1014272 : Path.checkChunk context decode facts instructions 1014272 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1014784 : Path.checkChunk context decode facts instructions 1014784 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1015296 : Path.checkChunk context decode facts instructions 1015296 512 = true := by
  decide +kernel

theorem sound_1007616 (prior : ∀ n, n < 1007616 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1015808 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1008128 := Path.chunk_sound context_valid decode facts instructions 1007616 512
    prior checked_1007616
  have h1008640 := Path.chunk_sound context_valid decode facts instructions 1008128 512
    h1008128 checked_1008128
  have h1009152 := Path.chunk_sound context_valid decode facts instructions 1008640 512
    h1008640 checked_1008640
  have h1009664 := Path.chunk_sound context_valid decode facts instructions 1009152 512
    h1009152 checked_1009152
  have h1010176 := Path.chunk_sound context_valid decode facts instructions 1009664 512
    h1009664 checked_1009664
  have h1010688 := Path.chunk_sound context_valid decode facts instructions 1010176 512
    h1010176 checked_1010176
  have h1011200 := Path.chunk_sound context_valid decode facts instructions 1010688 512
    h1010688 checked_1010688
  have h1011712 := Path.chunk_sound context_valid decode facts instructions 1011200 512
    h1011200 checked_1011200
  have h1012224 := Path.chunk_sound context_valid decode facts instructions 1011712 512
    h1011712 checked_1011712
  have h1012736 := Path.chunk_sound context_valid decode facts instructions 1012224 512
    h1012224 checked_1012224
  have h1013248 := Path.chunk_sound context_valid decode facts instructions 1012736 512
    h1012736 checked_1012736
  have h1013760 := Path.chunk_sound context_valid decode facts instructions 1013248 512
    h1013248 checked_1013248
  have h1014272 := Path.chunk_sound context_valid decode facts instructions 1013760 512
    h1013760 checked_1013760
  have h1014784 := Path.chunk_sound context_valid decode facts instructions 1014272 512
    h1014272 checked_1014272
  have h1015296 := Path.chunk_sound context_valid decode facts instructions 1014784 512
    h1014784 checked_1014784
  have h1015808 := Path.chunk_sound context_valid decode facts instructions 1015296 512
    h1015296 checked_1015296
  exact h1015808

end Sporadic.Janko3.AmalgamPresentation.Cover
