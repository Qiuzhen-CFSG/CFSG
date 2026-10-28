module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1269760 : Path.checkChunk context decode facts instructions 1269760 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1270272 : Path.checkChunk context decode facts instructions 1270272 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1270784 : Path.checkChunk context decode facts instructions 1270784 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1271296 : Path.checkChunk context decode facts instructions 1271296 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1271808 : Path.checkChunk context decode facts instructions 1271808 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1272320 : Path.checkChunk context decode facts instructions 1272320 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1272832 : Path.checkChunk context decode facts instructions 1272832 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1273344 : Path.checkChunk context decode facts instructions 1273344 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1273856 : Path.checkChunk context decode facts instructions 1273856 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1274368 : Path.checkChunk context decode facts instructions 1274368 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1274880 : Path.checkChunk context decode facts instructions 1274880 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1275392 : Path.checkChunk context decode facts instructions 1275392 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1275904 : Path.checkChunk context decode facts instructions 1275904 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1276416 : Path.checkChunk context decode facts instructions 1276416 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1276928 : Path.checkChunk context decode facts instructions 1276928 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1277440 : Path.checkChunk context decode facts instructions 1277440 512 = true := by
  decide +kernel

theorem sound_1269760 (prior : ∀ n, n < 1269760 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1277952 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1270272 := Path.chunk_sound context_valid decode facts instructions 1269760 512
    prior checked_1269760
  have h1270784 := Path.chunk_sound context_valid decode facts instructions 1270272 512
    h1270272 checked_1270272
  have h1271296 := Path.chunk_sound context_valid decode facts instructions 1270784 512
    h1270784 checked_1270784
  have h1271808 := Path.chunk_sound context_valid decode facts instructions 1271296 512
    h1271296 checked_1271296
  have h1272320 := Path.chunk_sound context_valid decode facts instructions 1271808 512
    h1271808 checked_1271808
  have h1272832 := Path.chunk_sound context_valid decode facts instructions 1272320 512
    h1272320 checked_1272320
  have h1273344 := Path.chunk_sound context_valid decode facts instructions 1272832 512
    h1272832 checked_1272832
  have h1273856 := Path.chunk_sound context_valid decode facts instructions 1273344 512
    h1273344 checked_1273344
  have h1274368 := Path.chunk_sound context_valid decode facts instructions 1273856 512
    h1273856 checked_1273856
  have h1274880 := Path.chunk_sound context_valid decode facts instructions 1274368 512
    h1274368 checked_1274368
  have h1275392 := Path.chunk_sound context_valid decode facts instructions 1274880 512
    h1274880 checked_1274880
  have h1275904 := Path.chunk_sound context_valid decode facts instructions 1275392 512
    h1275392 checked_1275392
  have h1276416 := Path.chunk_sound context_valid decode facts instructions 1275904 512
    h1275904 checked_1275904
  have h1276928 := Path.chunk_sound context_valid decode facts instructions 1276416 512
    h1276416 checked_1276416
  have h1277440 := Path.chunk_sound context_valid decode facts instructions 1276928 512
    h1276928 checked_1276928
  have h1277952 := Path.chunk_sound context_valid decode facts instructions 1277440 512
    h1277440 checked_1277440
  exact h1277952

end Sporadic.Janko3.AmalgamPresentation.Cover
