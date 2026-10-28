module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1064960 : Path.checkChunk context decode facts instructions 1064960 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1065472 : Path.checkChunk context decode facts instructions 1065472 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1065984 : Path.checkChunk context decode facts instructions 1065984 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1066496 : Path.checkChunk context decode facts instructions 1066496 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1067008 : Path.checkChunk context decode facts instructions 1067008 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1067520 : Path.checkChunk context decode facts instructions 1067520 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1068032 : Path.checkChunk context decode facts instructions 1068032 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1068544 : Path.checkChunk context decode facts instructions 1068544 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1069056 : Path.checkChunk context decode facts instructions 1069056 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1069568 : Path.checkChunk context decode facts instructions 1069568 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1070080 : Path.checkChunk context decode facts instructions 1070080 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1070592 : Path.checkChunk context decode facts instructions 1070592 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1071104 : Path.checkChunk context decode facts instructions 1071104 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1071616 : Path.checkChunk context decode facts instructions 1071616 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1072128 : Path.checkChunk context decode facts instructions 1072128 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1072640 : Path.checkChunk context decode facts instructions 1072640 512 = true := by
  decide +kernel

theorem sound_1064960 (prior : ∀ n, n < 1064960 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1073152 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1065472 := Path.chunk_sound context_valid decode facts instructions 1064960 512
    prior checked_1064960
  have h1065984 := Path.chunk_sound context_valid decode facts instructions 1065472 512
    h1065472 checked_1065472
  have h1066496 := Path.chunk_sound context_valid decode facts instructions 1065984 512
    h1065984 checked_1065984
  have h1067008 := Path.chunk_sound context_valid decode facts instructions 1066496 512
    h1066496 checked_1066496
  have h1067520 := Path.chunk_sound context_valid decode facts instructions 1067008 512
    h1067008 checked_1067008
  have h1068032 := Path.chunk_sound context_valid decode facts instructions 1067520 512
    h1067520 checked_1067520
  have h1068544 := Path.chunk_sound context_valid decode facts instructions 1068032 512
    h1068032 checked_1068032
  have h1069056 := Path.chunk_sound context_valid decode facts instructions 1068544 512
    h1068544 checked_1068544
  have h1069568 := Path.chunk_sound context_valid decode facts instructions 1069056 512
    h1069056 checked_1069056
  have h1070080 := Path.chunk_sound context_valid decode facts instructions 1069568 512
    h1069568 checked_1069568
  have h1070592 := Path.chunk_sound context_valid decode facts instructions 1070080 512
    h1070080 checked_1070080
  have h1071104 := Path.chunk_sound context_valid decode facts instructions 1070592 512
    h1070592 checked_1070592
  have h1071616 := Path.chunk_sound context_valid decode facts instructions 1071104 512
    h1071104 checked_1071104
  have h1072128 := Path.chunk_sound context_valid decode facts instructions 1071616 512
    h1071616 checked_1071616
  have h1072640 := Path.chunk_sound context_valid decode facts instructions 1072128 512
    h1072128 checked_1072128
  have h1073152 := Path.chunk_sound context_valid decode facts instructions 1072640 512
    h1072640 checked_1072640
  exact h1073152

end Sporadic.Janko3.AmalgamPresentation.Cover
