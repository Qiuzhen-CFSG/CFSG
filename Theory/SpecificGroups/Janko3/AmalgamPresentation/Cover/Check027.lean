module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_221184 : Path.checkChunk context decode facts instructions 221184 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_221696 : Path.checkChunk context decode facts instructions 221696 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_222208 : Path.checkChunk context decode facts instructions 222208 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_222720 : Path.checkChunk context decode facts instructions 222720 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_223232 : Path.checkChunk context decode facts instructions 223232 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_223744 : Path.checkChunk context decode facts instructions 223744 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_224256 : Path.checkChunk context decode facts instructions 224256 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_224768 : Path.checkChunk context decode facts instructions 224768 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_225280 : Path.checkChunk context decode facts instructions 225280 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_225792 : Path.checkChunk context decode facts instructions 225792 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_226304 : Path.checkChunk context decode facts instructions 226304 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_226816 : Path.checkChunk context decode facts instructions 226816 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_227328 : Path.checkChunk context decode facts instructions 227328 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_227840 : Path.checkChunk context decode facts instructions 227840 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_228352 : Path.checkChunk context decode facts instructions 228352 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_228864 : Path.checkChunk context decode facts instructions 228864 512 = true := by
  decide +kernel

theorem sound_221184 (prior : ∀ n, n < 221184 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 229376 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h221696 := Path.chunk_sound context_valid decode facts instructions 221184 512
    prior checked_221184
  have h222208 := Path.chunk_sound context_valid decode facts instructions 221696 512
    h221696 checked_221696
  have h222720 := Path.chunk_sound context_valid decode facts instructions 222208 512
    h222208 checked_222208
  have h223232 := Path.chunk_sound context_valid decode facts instructions 222720 512
    h222720 checked_222720
  have h223744 := Path.chunk_sound context_valid decode facts instructions 223232 512
    h223232 checked_223232
  have h224256 := Path.chunk_sound context_valid decode facts instructions 223744 512
    h223744 checked_223744
  have h224768 := Path.chunk_sound context_valid decode facts instructions 224256 512
    h224256 checked_224256
  have h225280 := Path.chunk_sound context_valid decode facts instructions 224768 512
    h224768 checked_224768
  have h225792 := Path.chunk_sound context_valid decode facts instructions 225280 512
    h225280 checked_225280
  have h226304 := Path.chunk_sound context_valid decode facts instructions 225792 512
    h225792 checked_225792
  have h226816 := Path.chunk_sound context_valid decode facts instructions 226304 512
    h226304 checked_226304
  have h227328 := Path.chunk_sound context_valid decode facts instructions 226816 512
    h226816 checked_226816
  have h227840 := Path.chunk_sound context_valid decode facts instructions 227328 512
    h227328 checked_227328
  have h228352 := Path.chunk_sound context_valid decode facts instructions 227840 512
    h227840 checked_227840
  have h228864 := Path.chunk_sound context_valid decode facts instructions 228352 512
    h228352 checked_228352
  have h229376 := Path.chunk_sound context_valid decode facts instructions 228864 512
    h228864 checked_228864
  exact h229376

end Sporadic.Janko3.AmalgamPresentation.Cover
