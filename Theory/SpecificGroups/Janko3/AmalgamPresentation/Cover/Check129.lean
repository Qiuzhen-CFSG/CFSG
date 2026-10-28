module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1056768 : Path.checkChunk context decode facts instructions 1056768 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1057280 : Path.checkChunk context decode facts instructions 1057280 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1057792 : Path.checkChunk context decode facts instructions 1057792 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1058304 : Path.checkChunk context decode facts instructions 1058304 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1058816 : Path.checkChunk context decode facts instructions 1058816 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1059328 : Path.checkChunk context decode facts instructions 1059328 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1059840 : Path.checkChunk context decode facts instructions 1059840 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1060352 : Path.checkChunk context decode facts instructions 1060352 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1060864 : Path.checkChunk context decode facts instructions 1060864 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1061376 : Path.checkChunk context decode facts instructions 1061376 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1061888 : Path.checkChunk context decode facts instructions 1061888 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1062400 : Path.checkChunk context decode facts instructions 1062400 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1062912 : Path.checkChunk context decode facts instructions 1062912 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1063424 : Path.checkChunk context decode facts instructions 1063424 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1063936 : Path.checkChunk context decode facts instructions 1063936 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1064448 : Path.checkChunk context decode facts instructions 1064448 512 = true := by
  decide +kernel

theorem sound_1056768 (prior : ∀ n, n < 1056768 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1064960 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1057280 := Path.chunk_sound context_valid decode facts instructions 1056768 512
    prior checked_1056768
  have h1057792 := Path.chunk_sound context_valid decode facts instructions 1057280 512
    h1057280 checked_1057280
  have h1058304 := Path.chunk_sound context_valid decode facts instructions 1057792 512
    h1057792 checked_1057792
  have h1058816 := Path.chunk_sound context_valid decode facts instructions 1058304 512
    h1058304 checked_1058304
  have h1059328 := Path.chunk_sound context_valid decode facts instructions 1058816 512
    h1058816 checked_1058816
  have h1059840 := Path.chunk_sound context_valid decode facts instructions 1059328 512
    h1059328 checked_1059328
  have h1060352 := Path.chunk_sound context_valid decode facts instructions 1059840 512
    h1059840 checked_1059840
  have h1060864 := Path.chunk_sound context_valid decode facts instructions 1060352 512
    h1060352 checked_1060352
  have h1061376 := Path.chunk_sound context_valid decode facts instructions 1060864 512
    h1060864 checked_1060864
  have h1061888 := Path.chunk_sound context_valid decode facts instructions 1061376 512
    h1061376 checked_1061376
  have h1062400 := Path.chunk_sound context_valid decode facts instructions 1061888 512
    h1061888 checked_1061888
  have h1062912 := Path.chunk_sound context_valid decode facts instructions 1062400 512
    h1062400 checked_1062400
  have h1063424 := Path.chunk_sound context_valid decode facts instructions 1062912 512
    h1062912 checked_1062912
  have h1063936 := Path.chunk_sound context_valid decode facts instructions 1063424 512
    h1063424 checked_1063424
  have h1064448 := Path.chunk_sound context_valid decode facts instructions 1063936 512
    h1063936 checked_1063936
  have h1064960 := Path.chunk_sound context_valid decode facts instructions 1064448 512
    h1064448 checked_1064448
  exact h1064960

end Sporadic.Janko3.AmalgamPresentation.Cover
