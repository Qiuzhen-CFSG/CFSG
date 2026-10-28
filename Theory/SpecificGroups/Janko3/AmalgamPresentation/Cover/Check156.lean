module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1277952 : Path.checkChunk context decode facts instructions 1277952 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1278464 : Path.checkChunk context decode facts instructions 1278464 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1278976 : Path.checkChunk context decode facts instructions 1278976 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1279488 : Path.checkChunk context decode facts instructions 1279488 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1280000 : Path.checkChunk context decode facts instructions 1280000 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1280512 : Path.checkChunk context decode facts instructions 1280512 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1281024 : Path.checkChunk context decode facts instructions 1281024 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1281536 : Path.checkChunk context decode facts instructions 1281536 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1282048 : Path.checkChunk context decode facts instructions 1282048 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1282560 : Path.checkChunk context decode facts instructions 1282560 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1283072 : Path.checkChunk context decode facts instructions 1283072 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1283584 : Path.checkChunk context decode facts instructions 1283584 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1284096 : Path.checkChunk context decode facts instructions 1284096 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1284608 : Path.checkChunk context decode facts instructions 1284608 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1285120 : Path.checkChunk context decode facts instructions 1285120 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1285632 : Path.checkChunk context decode facts instructions 1285632 512 = true := by
  decide +kernel

theorem sound_1277952 (prior : ∀ n, n < 1277952 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1286144 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1278464 := Path.chunk_sound context_valid decode facts instructions 1277952 512
    prior checked_1277952
  have h1278976 := Path.chunk_sound context_valid decode facts instructions 1278464 512
    h1278464 checked_1278464
  have h1279488 := Path.chunk_sound context_valid decode facts instructions 1278976 512
    h1278976 checked_1278976
  have h1280000 := Path.chunk_sound context_valid decode facts instructions 1279488 512
    h1279488 checked_1279488
  have h1280512 := Path.chunk_sound context_valid decode facts instructions 1280000 512
    h1280000 checked_1280000
  have h1281024 := Path.chunk_sound context_valid decode facts instructions 1280512 512
    h1280512 checked_1280512
  have h1281536 := Path.chunk_sound context_valid decode facts instructions 1281024 512
    h1281024 checked_1281024
  have h1282048 := Path.chunk_sound context_valid decode facts instructions 1281536 512
    h1281536 checked_1281536
  have h1282560 := Path.chunk_sound context_valid decode facts instructions 1282048 512
    h1282048 checked_1282048
  have h1283072 := Path.chunk_sound context_valid decode facts instructions 1282560 512
    h1282560 checked_1282560
  have h1283584 := Path.chunk_sound context_valid decode facts instructions 1283072 512
    h1283072 checked_1283072
  have h1284096 := Path.chunk_sound context_valid decode facts instructions 1283584 512
    h1283584 checked_1283584
  have h1284608 := Path.chunk_sound context_valid decode facts instructions 1284096 512
    h1284096 checked_1284096
  have h1285120 := Path.chunk_sound context_valid decode facts instructions 1284608 512
    h1284608 checked_1284608
  have h1285632 := Path.chunk_sound context_valid decode facts instructions 1285120 512
    h1285120 checked_1285120
  have h1286144 := Path.chunk_sound context_valid decode facts instructions 1285632 512
    h1285632 checked_1285632
  exact h1286144

end Sporadic.Janko3.AmalgamPresentation.Cover
