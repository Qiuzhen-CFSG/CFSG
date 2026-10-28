module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1310720 : Path.checkChunk context decode facts instructions 1310720 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1311232 : Path.checkChunk context decode facts instructions 1311232 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1311744 : Path.checkChunk context decode facts instructions 1311744 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1312256 : Path.checkChunk context decode facts instructions 1312256 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1312768 : Path.checkChunk context decode facts instructions 1312768 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1313280 : Path.checkChunk context decode facts instructions 1313280 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1313792 : Path.checkChunk context decode facts instructions 1313792 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1314304 : Path.checkChunk context decode facts instructions 1314304 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1314816 : Path.checkChunk context decode facts instructions 1314816 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1315328 : Path.checkChunk context decode facts instructions 1315328 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1315840 : Path.checkChunk context decode facts instructions 1315840 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1316352 : Path.checkChunk context decode facts instructions 1316352 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1316864 : Path.checkChunk context decode facts instructions 1316864 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1317376 : Path.checkChunk context decode facts instructions 1317376 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1317888 : Path.checkChunk context decode facts instructions 1317888 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1318400 : Path.checkChunk context decode facts instructions 1318400 512 = true := by
  decide +kernel

theorem sound_1310720 (prior : ∀ n, n < 1310720 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1318912 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1311232 := Path.chunk_sound context_valid decode facts instructions 1310720 512
    prior checked_1310720
  have h1311744 := Path.chunk_sound context_valid decode facts instructions 1311232 512
    h1311232 checked_1311232
  have h1312256 := Path.chunk_sound context_valid decode facts instructions 1311744 512
    h1311744 checked_1311744
  have h1312768 := Path.chunk_sound context_valid decode facts instructions 1312256 512
    h1312256 checked_1312256
  have h1313280 := Path.chunk_sound context_valid decode facts instructions 1312768 512
    h1312768 checked_1312768
  have h1313792 := Path.chunk_sound context_valid decode facts instructions 1313280 512
    h1313280 checked_1313280
  have h1314304 := Path.chunk_sound context_valid decode facts instructions 1313792 512
    h1313792 checked_1313792
  have h1314816 := Path.chunk_sound context_valid decode facts instructions 1314304 512
    h1314304 checked_1314304
  have h1315328 := Path.chunk_sound context_valid decode facts instructions 1314816 512
    h1314816 checked_1314816
  have h1315840 := Path.chunk_sound context_valid decode facts instructions 1315328 512
    h1315328 checked_1315328
  have h1316352 := Path.chunk_sound context_valid decode facts instructions 1315840 512
    h1315840 checked_1315840
  have h1316864 := Path.chunk_sound context_valid decode facts instructions 1316352 512
    h1316352 checked_1316352
  have h1317376 := Path.chunk_sound context_valid decode facts instructions 1316864 512
    h1316864 checked_1316864
  have h1317888 := Path.chunk_sound context_valid decode facts instructions 1317376 512
    h1317376 checked_1317376
  have h1318400 := Path.chunk_sound context_valid decode facts instructions 1317888 512
    h1317888 checked_1317888
  have h1318912 := Path.chunk_sound context_valid decode facts instructions 1318400 512
    h1318400 checked_1318400
  exact h1318912

end Sporadic.Janko3.AmalgamPresentation.Cover
