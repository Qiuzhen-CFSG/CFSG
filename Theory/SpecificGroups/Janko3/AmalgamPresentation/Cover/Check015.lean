module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_122880 : Path.checkChunk context decode facts instructions 122880 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_123392 : Path.checkChunk context decode facts instructions 123392 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_123904 : Path.checkChunk context decode facts instructions 123904 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_124416 : Path.checkChunk context decode facts instructions 124416 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_124928 : Path.checkChunk context decode facts instructions 124928 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_125440 : Path.checkChunk context decode facts instructions 125440 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_125952 : Path.checkChunk context decode facts instructions 125952 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_126464 : Path.checkChunk context decode facts instructions 126464 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_126976 : Path.checkChunk context decode facts instructions 126976 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_127488 : Path.checkChunk context decode facts instructions 127488 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_128000 : Path.checkChunk context decode facts instructions 128000 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_128512 : Path.checkChunk context decode facts instructions 128512 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_129024 : Path.checkChunk context decode facts instructions 129024 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_129536 : Path.checkChunk context decode facts instructions 129536 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_130048 : Path.checkChunk context decode facts instructions 130048 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_130560 : Path.checkChunk context decode facts instructions 130560 512 = true := by
  decide +kernel

theorem sound_122880 (prior : ∀ n, n < 122880 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 131072 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h123392 := Path.chunk_sound context_valid decode facts instructions 122880 512
    prior checked_122880
  have h123904 := Path.chunk_sound context_valid decode facts instructions 123392 512
    h123392 checked_123392
  have h124416 := Path.chunk_sound context_valid decode facts instructions 123904 512
    h123904 checked_123904
  have h124928 := Path.chunk_sound context_valid decode facts instructions 124416 512
    h124416 checked_124416
  have h125440 := Path.chunk_sound context_valid decode facts instructions 124928 512
    h124928 checked_124928
  have h125952 := Path.chunk_sound context_valid decode facts instructions 125440 512
    h125440 checked_125440
  have h126464 := Path.chunk_sound context_valid decode facts instructions 125952 512
    h125952 checked_125952
  have h126976 := Path.chunk_sound context_valid decode facts instructions 126464 512
    h126464 checked_126464
  have h127488 := Path.chunk_sound context_valid decode facts instructions 126976 512
    h126976 checked_126976
  have h128000 := Path.chunk_sound context_valid decode facts instructions 127488 512
    h127488 checked_127488
  have h128512 := Path.chunk_sound context_valid decode facts instructions 128000 512
    h128000 checked_128000
  have h129024 := Path.chunk_sound context_valid decode facts instructions 128512 512
    h128512 checked_128512
  have h129536 := Path.chunk_sound context_valid decode facts instructions 129024 512
    h129024 checked_129024
  have h130048 := Path.chunk_sound context_valid decode facts instructions 129536 512
    h129536 checked_129536
  have h130560 := Path.chunk_sound context_valid decode facts instructions 130048 512
    h130048 checked_130048
  have h131072 := Path.chunk_sound context_valid decode facts instructions 130560 512
    h130560 checked_130560
  exact h131072

end Sporadic.Janko3.AmalgamPresentation.Cover
