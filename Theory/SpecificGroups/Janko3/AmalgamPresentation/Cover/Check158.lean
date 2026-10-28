module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1294336 : Path.checkChunk context decode facts instructions 1294336 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1294848 : Path.checkChunk context decode facts instructions 1294848 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1295360 : Path.checkChunk context decode facts instructions 1295360 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1295872 : Path.checkChunk context decode facts instructions 1295872 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1296384 : Path.checkChunk context decode facts instructions 1296384 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1296896 : Path.checkChunk context decode facts instructions 1296896 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1297408 : Path.checkChunk context decode facts instructions 1297408 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1297920 : Path.checkChunk context decode facts instructions 1297920 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1298432 : Path.checkChunk context decode facts instructions 1298432 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1298944 : Path.checkChunk context decode facts instructions 1298944 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1299456 : Path.checkChunk context decode facts instructions 1299456 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1299968 : Path.checkChunk context decode facts instructions 1299968 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1300480 : Path.checkChunk context decode facts instructions 1300480 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1300992 : Path.checkChunk context decode facts instructions 1300992 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1301504 : Path.checkChunk context decode facts instructions 1301504 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1302016 : Path.checkChunk context decode facts instructions 1302016 512 = true := by
  decide +kernel

theorem sound_1294336 (prior : ∀ n, n < 1294336 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1302528 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1294848 := Path.chunk_sound context_valid decode facts instructions 1294336 512
    prior checked_1294336
  have h1295360 := Path.chunk_sound context_valid decode facts instructions 1294848 512
    h1294848 checked_1294848
  have h1295872 := Path.chunk_sound context_valid decode facts instructions 1295360 512
    h1295360 checked_1295360
  have h1296384 := Path.chunk_sound context_valid decode facts instructions 1295872 512
    h1295872 checked_1295872
  have h1296896 := Path.chunk_sound context_valid decode facts instructions 1296384 512
    h1296384 checked_1296384
  have h1297408 := Path.chunk_sound context_valid decode facts instructions 1296896 512
    h1296896 checked_1296896
  have h1297920 := Path.chunk_sound context_valid decode facts instructions 1297408 512
    h1297408 checked_1297408
  have h1298432 := Path.chunk_sound context_valid decode facts instructions 1297920 512
    h1297920 checked_1297920
  have h1298944 := Path.chunk_sound context_valid decode facts instructions 1298432 512
    h1298432 checked_1298432
  have h1299456 := Path.chunk_sound context_valid decode facts instructions 1298944 512
    h1298944 checked_1298944
  have h1299968 := Path.chunk_sound context_valid decode facts instructions 1299456 512
    h1299456 checked_1299456
  have h1300480 := Path.chunk_sound context_valid decode facts instructions 1299968 512
    h1299968 checked_1299968
  have h1300992 := Path.chunk_sound context_valid decode facts instructions 1300480 512
    h1300480 checked_1300480
  have h1301504 := Path.chunk_sound context_valid decode facts instructions 1300992 512
    h1300992 checked_1300992
  have h1302016 := Path.chunk_sound context_valid decode facts instructions 1301504 512
    h1301504 checked_1301504
  have h1302528 := Path.chunk_sound context_valid decode facts instructions 1302016 512
    h1302016 checked_1302016
  exact h1302528

end Sporadic.Janko3.AmalgamPresentation.Cover
