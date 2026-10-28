module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_212992 : Path.checkChunk context decode facts instructions 212992 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_213504 : Path.checkChunk context decode facts instructions 213504 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_214016 : Path.checkChunk context decode facts instructions 214016 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_214528 : Path.checkChunk context decode facts instructions 214528 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_215040 : Path.checkChunk context decode facts instructions 215040 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_215552 : Path.checkChunk context decode facts instructions 215552 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_216064 : Path.checkChunk context decode facts instructions 216064 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_216576 : Path.checkChunk context decode facts instructions 216576 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_217088 : Path.checkChunk context decode facts instructions 217088 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_217600 : Path.checkChunk context decode facts instructions 217600 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_218112 : Path.checkChunk context decode facts instructions 218112 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_218624 : Path.checkChunk context decode facts instructions 218624 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_219136 : Path.checkChunk context decode facts instructions 219136 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_219648 : Path.checkChunk context decode facts instructions 219648 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_220160 : Path.checkChunk context decode facts instructions 220160 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_220672 : Path.checkChunk context decode facts instructions 220672 512 = true := by
  decide +kernel

theorem sound_212992 (prior : ∀ n, n < 212992 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 221184 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h213504 := Path.chunk_sound context_valid decode facts instructions 212992 512
    prior checked_212992
  have h214016 := Path.chunk_sound context_valid decode facts instructions 213504 512
    h213504 checked_213504
  have h214528 := Path.chunk_sound context_valid decode facts instructions 214016 512
    h214016 checked_214016
  have h215040 := Path.chunk_sound context_valid decode facts instructions 214528 512
    h214528 checked_214528
  have h215552 := Path.chunk_sound context_valid decode facts instructions 215040 512
    h215040 checked_215040
  have h216064 := Path.chunk_sound context_valid decode facts instructions 215552 512
    h215552 checked_215552
  have h216576 := Path.chunk_sound context_valid decode facts instructions 216064 512
    h216064 checked_216064
  have h217088 := Path.chunk_sound context_valid decode facts instructions 216576 512
    h216576 checked_216576
  have h217600 := Path.chunk_sound context_valid decode facts instructions 217088 512
    h217088 checked_217088
  have h218112 := Path.chunk_sound context_valid decode facts instructions 217600 512
    h217600 checked_217600
  have h218624 := Path.chunk_sound context_valid decode facts instructions 218112 512
    h218112 checked_218112
  have h219136 := Path.chunk_sound context_valid decode facts instructions 218624 512
    h218624 checked_218624
  have h219648 := Path.chunk_sound context_valid decode facts instructions 219136 512
    h219136 checked_219136
  have h220160 := Path.chunk_sound context_valid decode facts instructions 219648 512
    h219648 checked_219648
  have h220672 := Path.chunk_sound context_valid decode facts instructions 220160 512
    h220160 checked_220160
  have h221184 := Path.chunk_sound context_valid decode facts instructions 220672 512
    h220672 checked_220672
  exact h221184

end Sporadic.Janko3.AmalgamPresentation.Cover
