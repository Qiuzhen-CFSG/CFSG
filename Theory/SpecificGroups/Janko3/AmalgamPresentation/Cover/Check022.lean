module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_180224 : Path.checkChunk context decode facts instructions 180224 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_180736 : Path.checkChunk context decode facts instructions 180736 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_181248 : Path.checkChunk context decode facts instructions 181248 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_181760 : Path.checkChunk context decode facts instructions 181760 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_182272 : Path.checkChunk context decode facts instructions 182272 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_182784 : Path.checkChunk context decode facts instructions 182784 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_183296 : Path.checkChunk context decode facts instructions 183296 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_183808 : Path.checkChunk context decode facts instructions 183808 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_184320 : Path.checkChunk context decode facts instructions 184320 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_184832 : Path.checkChunk context decode facts instructions 184832 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_185344 : Path.checkChunk context decode facts instructions 185344 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_185856 : Path.checkChunk context decode facts instructions 185856 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_186368 : Path.checkChunk context decode facts instructions 186368 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_186880 : Path.checkChunk context decode facts instructions 186880 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_187392 : Path.checkChunk context decode facts instructions 187392 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_187904 : Path.checkChunk context decode facts instructions 187904 512 = true := by
  decide +kernel

theorem sound_180224 (prior : ∀ n, n < 180224 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 188416 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h180736 := Path.chunk_sound context_valid decode facts instructions 180224 512
    prior checked_180224
  have h181248 := Path.chunk_sound context_valid decode facts instructions 180736 512
    h180736 checked_180736
  have h181760 := Path.chunk_sound context_valid decode facts instructions 181248 512
    h181248 checked_181248
  have h182272 := Path.chunk_sound context_valid decode facts instructions 181760 512
    h181760 checked_181760
  have h182784 := Path.chunk_sound context_valid decode facts instructions 182272 512
    h182272 checked_182272
  have h183296 := Path.chunk_sound context_valid decode facts instructions 182784 512
    h182784 checked_182784
  have h183808 := Path.chunk_sound context_valid decode facts instructions 183296 512
    h183296 checked_183296
  have h184320 := Path.chunk_sound context_valid decode facts instructions 183808 512
    h183808 checked_183808
  have h184832 := Path.chunk_sound context_valid decode facts instructions 184320 512
    h184320 checked_184320
  have h185344 := Path.chunk_sound context_valid decode facts instructions 184832 512
    h184832 checked_184832
  have h185856 := Path.chunk_sound context_valid decode facts instructions 185344 512
    h185344 checked_185344
  have h186368 := Path.chunk_sound context_valid decode facts instructions 185856 512
    h185856 checked_185856
  have h186880 := Path.chunk_sound context_valid decode facts instructions 186368 512
    h186368 checked_186368
  have h187392 := Path.chunk_sound context_valid decode facts instructions 186880 512
    h186880 checked_186880
  have h187904 := Path.chunk_sound context_valid decode facts instructions 187392 512
    h187392 checked_187392
  have h188416 := Path.chunk_sound context_valid decode facts instructions 187904 512
    h187904 checked_187904
  exact h188416

end Sporadic.Janko3.AmalgamPresentation.Cover
