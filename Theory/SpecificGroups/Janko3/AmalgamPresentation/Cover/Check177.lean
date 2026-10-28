module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1449984 : Path.checkChunk context decode facts instructions 1449984 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1450496 : Path.checkChunk context decode facts instructions 1450496 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1451008 : Path.checkChunk context decode facts instructions 1451008 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1451520 : Path.checkChunk context decode facts instructions 1451520 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1452032 : Path.checkChunk context decode facts instructions 1452032 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1452544 : Path.checkChunk context decode facts instructions 1452544 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1453056 : Path.checkChunk context decode facts instructions 1453056 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1453568 : Path.checkChunk context decode facts instructions 1453568 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1454080 : Path.checkChunk context decode facts instructions 1454080 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1454592 : Path.checkChunk context decode facts instructions 1454592 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1455104 : Path.checkChunk context decode facts instructions 1455104 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1455616 : Path.checkChunk context decode facts instructions 1455616 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1456128 : Path.checkChunk context decode facts instructions 1456128 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1456640 : Path.checkChunk context decode facts instructions 1456640 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1457152 : Path.checkChunk context decode facts instructions 1457152 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1457664 : Path.checkChunk context decode facts instructions 1457664 512 = true := by
  decide +kernel

theorem sound_1449984 (prior : ∀ n, n < 1449984 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1458176 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1450496 := Path.chunk_sound context_valid decode facts instructions 1449984 512
    prior checked_1449984
  have h1451008 := Path.chunk_sound context_valid decode facts instructions 1450496 512
    h1450496 checked_1450496
  have h1451520 := Path.chunk_sound context_valid decode facts instructions 1451008 512
    h1451008 checked_1451008
  have h1452032 := Path.chunk_sound context_valid decode facts instructions 1451520 512
    h1451520 checked_1451520
  have h1452544 := Path.chunk_sound context_valid decode facts instructions 1452032 512
    h1452032 checked_1452032
  have h1453056 := Path.chunk_sound context_valid decode facts instructions 1452544 512
    h1452544 checked_1452544
  have h1453568 := Path.chunk_sound context_valid decode facts instructions 1453056 512
    h1453056 checked_1453056
  have h1454080 := Path.chunk_sound context_valid decode facts instructions 1453568 512
    h1453568 checked_1453568
  have h1454592 := Path.chunk_sound context_valid decode facts instructions 1454080 512
    h1454080 checked_1454080
  have h1455104 := Path.chunk_sound context_valid decode facts instructions 1454592 512
    h1454592 checked_1454592
  have h1455616 := Path.chunk_sound context_valid decode facts instructions 1455104 512
    h1455104 checked_1455104
  have h1456128 := Path.chunk_sound context_valid decode facts instructions 1455616 512
    h1455616 checked_1455616
  have h1456640 := Path.chunk_sound context_valid decode facts instructions 1456128 512
    h1456128 checked_1456128
  have h1457152 := Path.chunk_sound context_valid decode facts instructions 1456640 512
    h1456640 checked_1456640
  have h1457664 := Path.chunk_sound context_valid decode facts instructions 1457152 512
    h1457152 checked_1457152
  have h1458176 := Path.chunk_sound context_valid decode facts instructions 1457664 512
    h1457664 checked_1457664
  exact h1458176

end Sporadic.Janko3.AmalgamPresentation.Cover
