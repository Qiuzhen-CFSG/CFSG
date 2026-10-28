module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_229376 : Path.checkChunk context decode facts instructions 229376 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_229888 : Path.checkChunk context decode facts instructions 229888 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_230400 : Path.checkChunk context decode facts instructions 230400 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_230912 : Path.checkChunk context decode facts instructions 230912 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_231424 : Path.checkChunk context decode facts instructions 231424 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_231936 : Path.checkChunk context decode facts instructions 231936 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_232448 : Path.checkChunk context decode facts instructions 232448 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_232960 : Path.checkChunk context decode facts instructions 232960 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_233472 : Path.checkChunk context decode facts instructions 233472 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_233984 : Path.checkChunk context decode facts instructions 233984 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_234496 : Path.checkChunk context decode facts instructions 234496 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_235008 : Path.checkChunk context decode facts instructions 235008 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_235520 : Path.checkChunk context decode facts instructions 235520 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_236032 : Path.checkChunk context decode facts instructions 236032 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_236544 : Path.checkChunk context decode facts instructions 236544 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_237056 : Path.checkChunk context decode facts instructions 237056 512 = true := by
  decide +kernel

theorem sound_229376 (prior : ∀ n, n < 229376 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 237568 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h229888 := Path.chunk_sound context_valid decode facts instructions 229376 512
    prior checked_229376
  have h230400 := Path.chunk_sound context_valid decode facts instructions 229888 512
    h229888 checked_229888
  have h230912 := Path.chunk_sound context_valid decode facts instructions 230400 512
    h230400 checked_230400
  have h231424 := Path.chunk_sound context_valid decode facts instructions 230912 512
    h230912 checked_230912
  have h231936 := Path.chunk_sound context_valid decode facts instructions 231424 512
    h231424 checked_231424
  have h232448 := Path.chunk_sound context_valid decode facts instructions 231936 512
    h231936 checked_231936
  have h232960 := Path.chunk_sound context_valid decode facts instructions 232448 512
    h232448 checked_232448
  have h233472 := Path.chunk_sound context_valid decode facts instructions 232960 512
    h232960 checked_232960
  have h233984 := Path.chunk_sound context_valid decode facts instructions 233472 512
    h233472 checked_233472
  have h234496 := Path.chunk_sound context_valid decode facts instructions 233984 512
    h233984 checked_233984
  have h235008 := Path.chunk_sound context_valid decode facts instructions 234496 512
    h234496 checked_234496
  have h235520 := Path.chunk_sound context_valid decode facts instructions 235008 512
    h235008 checked_235008
  have h236032 := Path.chunk_sound context_valid decode facts instructions 235520 512
    h235520 checked_235520
  have h236544 := Path.chunk_sound context_valid decode facts instructions 236032 512
    h236032 checked_236032
  have h237056 := Path.chunk_sound context_valid decode facts instructions 236544 512
    h236544 checked_236544
  have h237568 := Path.chunk_sound context_valid decode facts instructions 237056 512
    h237056 checked_237056
  exact h237568

end Sporadic.Janko3.AmalgamPresentation.Cover
