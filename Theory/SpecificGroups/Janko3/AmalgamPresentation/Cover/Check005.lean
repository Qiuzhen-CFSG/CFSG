module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_40960 : Path.checkChunk context decode facts instructions 40960 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_41472 : Path.checkChunk context decode facts instructions 41472 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_41984 : Path.checkChunk context decode facts instructions 41984 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_42496 : Path.checkChunk context decode facts instructions 42496 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_43008 : Path.checkChunk context decode facts instructions 43008 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_43520 : Path.checkChunk context decode facts instructions 43520 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_44032 : Path.checkChunk context decode facts instructions 44032 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_44544 : Path.checkChunk context decode facts instructions 44544 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_45056 : Path.checkChunk context decode facts instructions 45056 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_45568 : Path.checkChunk context decode facts instructions 45568 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_46080 : Path.checkChunk context decode facts instructions 46080 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_46592 : Path.checkChunk context decode facts instructions 46592 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_47104 : Path.checkChunk context decode facts instructions 47104 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_47616 : Path.checkChunk context decode facts instructions 47616 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_48128 : Path.checkChunk context decode facts instructions 48128 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_48640 : Path.checkChunk context decode facts instructions 48640 512 = true := by
  decide +kernel

theorem sound_40960 (prior : ∀ n, n < 40960 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 49152 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h41472 := Path.chunk_sound context_valid decode facts instructions 40960 512
    prior checked_40960
  have h41984 := Path.chunk_sound context_valid decode facts instructions 41472 512
    h41472 checked_41472
  have h42496 := Path.chunk_sound context_valid decode facts instructions 41984 512
    h41984 checked_41984
  have h43008 := Path.chunk_sound context_valid decode facts instructions 42496 512
    h42496 checked_42496
  have h43520 := Path.chunk_sound context_valid decode facts instructions 43008 512
    h43008 checked_43008
  have h44032 := Path.chunk_sound context_valid decode facts instructions 43520 512
    h43520 checked_43520
  have h44544 := Path.chunk_sound context_valid decode facts instructions 44032 512
    h44032 checked_44032
  have h45056 := Path.chunk_sound context_valid decode facts instructions 44544 512
    h44544 checked_44544
  have h45568 := Path.chunk_sound context_valid decode facts instructions 45056 512
    h45056 checked_45056
  have h46080 := Path.chunk_sound context_valid decode facts instructions 45568 512
    h45568 checked_45568
  have h46592 := Path.chunk_sound context_valid decode facts instructions 46080 512
    h46080 checked_46080
  have h47104 := Path.chunk_sound context_valid decode facts instructions 46592 512
    h46592 checked_46592
  have h47616 := Path.chunk_sound context_valid decode facts instructions 47104 512
    h47104 checked_47104
  have h48128 := Path.chunk_sound context_valid decode facts instructions 47616 512
    h47616 checked_47616
  have h48640 := Path.chunk_sound context_valid decode facts instructions 48128 512
    h48128 checked_48128
  have h49152 := Path.chunk_sound context_valid decode facts instructions 48640 512
    h48640 checked_48640
  exact h49152

end Sporadic.Janko3.AmalgamPresentation.Cover
