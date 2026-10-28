module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1146880 : Path.checkChunk context decode facts instructions 1146880 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1147392 : Path.checkChunk context decode facts instructions 1147392 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1147904 : Path.checkChunk context decode facts instructions 1147904 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1148416 : Path.checkChunk context decode facts instructions 1148416 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1148928 : Path.checkChunk context decode facts instructions 1148928 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1149440 : Path.checkChunk context decode facts instructions 1149440 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1149952 : Path.checkChunk context decode facts instructions 1149952 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1150464 : Path.checkChunk context decode facts instructions 1150464 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1150976 : Path.checkChunk context decode facts instructions 1150976 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1151488 : Path.checkChunk context decode facts instructions 1151488 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1152000 : Path.checkChunk context decode facts instructions 1152000 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1152512 : Path.checkChunk context decode facts instructions 1152512 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1153024 : Path.checkChunk context decode facts instructions 1153024 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1153536 : Path.checkChunk context decode facts instructions 1153536 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1154048 : Path.checkChunk context decode facts instructions 1154048 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1154560 : Path.checkChunk context decode facts instructions 1154560 512 = true := by
  decide +kernel

theorem sound_1146880 (prior : ∀ n, n < 1146880 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1155072 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1147392 := Path.chunk_sound context_valid decode facts instructions 1146880 512
    prior checked_1146880
  have h1147904 := Path.chunk_sound context_valid decode facts instructions 1147392 512
    h1147392 checked_1147392
  have h1148416 := Path.chunk_sound context_valid decode facts instructions 1147904 512
    h1147904 checked_1147904
  have h1148928 := Path.chunk_sound context_valid decode facts instructions 1148416 512
    h1148416 checked_1148416
  have h1149440 := Path.chunk_sound context_valid decode facts instructions 1148928 512
    h1148928 checked_1148928
  have h1149952 := Path.chunk_sound context_valid decode facts instructions 1149440 512
    h1149440 checked_1149440
  have h1150464 := Path.chunk_sound context_valid decode facts instructions 1149952 512
    h1149952 checked_1149952
  have h1150976 := Path.chunk_sound context_valid decode facts instructions 1150464 512
    h1150464 checked_1150464
  have h1151488 := Path.chunk_sound context_valid decode facts instructions 1150976 512
    h1150976 checked_1150976
  have h1152000 := Path.chunk_sound context_valid decode facts instructions 1151488 512
    h1151488 checked_1151488
  have h1152512 := Path.chunk_sound context_valid decode facts instructions 1152000 512
    h1152000 checked_1152000
  have h1153024 := Path.chunk_sound context_valid decode facts instructions 1152512 512
    h1152512 checked_1152512
  have h1153536 := Path.chunk_sound context_valid decode facts instructions 1153024 512
    h1153024 checked_1153024
  have h1154048 := Path.chunk_sound context_valid decode facts instructions 1153536 512
    h1153536 checked_1153536
  have h1154560 := Path.chunk_sound context_valid decode facts instructions 1154048 512
    h1154048 checked_1154048
  have h1155072 := Path.chunk_sound context_valid decode facts instructions 1154560 512
    h1154560 checked_1154560
  exact h1155072

end Sporadic.Janko3.AmalgamPresentation.Cover
