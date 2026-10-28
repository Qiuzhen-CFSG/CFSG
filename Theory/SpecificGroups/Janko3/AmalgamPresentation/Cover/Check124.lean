module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1015808 : Path.checkChunk context decode facts instructions 1015808 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1016320 : Path.checkChunk context decode facts instructions 1016320 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1016832 : Path.checkChunk context decode facts instructions 1016832 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1017344 : Path.checkChunk context decode facts instructions 1017344 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1017856 : Path.checkChunk context decode facts instructions 1017856 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1018368 : Path.checkChunk context decode facts instructions 1018368 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1018880 : Path.checkChunk context decode facts instructions 1018880 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1019392 : Path.checkChunk context decode facts instructions 1019392 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1019904 : Path.checkChunk context decode facts instructions 1019904 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1020416 : Path.checkChunk context decode facts instructions 1020416 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1020928 : Path.checkChunk context decode facts instructions 1020928 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1021440 : Path.checkChunk context decode facts instructions 1021440 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1021952 : Path.checkChunk context decode facts instructions 1021952 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1022464 : Path.checkChunk context decode facts instructions 1022464 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1022976 : Path.checkChunk context decode facts instructions 1022976 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1023488 : Path.checkChunk context decode facts instructions 1023488 512 = true := by
  decide +kernel

theorem sound_1015808 (prior : ∀ n, n < 1015808 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1024000 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1016320 := Path.chunk_sound context_valid decode facts instructions 1015808 512
    prior checked_1015808
  have h1016832 := Path.chunk_sound context_valid decode facts instructions 1016320 512
    h1016320 checked_1016320
  have h1017344 := Path.chunk_sound context_valid decode facts instructions 1016832 512
    h1016832 checked_1016832
  have h1017856 := Path.chunk_sound context_valid decode facts instructions 1017344 512
    h1017344 checked_1017344
  have h1018368 := Path.chunk_sound context_valid decode facts instructions 1017856 512
    h1017856 checked_1017856
  have h1018880 := Path.chunk_sound context_valid decode facts instructions 1018368 512
    h1018368 checked_1018368
  have h1019392 := Path.chunk_sound context_valid decode facts instructions 1018880 512
    h1018880 checked_1018880
  have h1019904 := Path.chunk_sound context_valid decode facts instructions 1019392 512
    h1019392 checked_1019392
  have h1020416 := Path.chunk_sound context_valid decode facts instructions 1019904 512
    h1019904 checked_1019904
  have h1020928 := Path.chunk_sound context_valid decode facts instructions 1020416 512
    h1020416 checked_1020416
  have h1021440 := Path.chunk_sound context_valid decode facts instructions 1020928 512
    h1020928 checked_1020928
  have h1021952 := Path.chunk_sound context_valid decode facts instructions 1021440 512
    h1021440 checked_1021440
  have h1022464 := Path.chunk_sound context_valid decode facts instructions 1021952 512
    h1021952 checked_1021952
  have h1022976 := Path.chunk_sound context_valid decode facts instructions 1022464 512
    h1022464 checked_1022464
  have h1023488 := Path.chunk_sound context_valid decode facts instructions 1022976 512
    h1022976 checked_1022976
  have h1024000 := Path.chunk_sound context_valid decode facts instructions 1023488 512
    h1023488 checked_1023488
  exact h1024000

end Sporadic.Janko3.AmalgamPresentation.Cover
