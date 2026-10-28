module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1409024 : Path.checkChunk context decode facts instructions 1409024 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1409536 : Path.checkChunk context decode facts instructions 1409536 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1410048 : Path.checkChunk context decode facts instructions 1410048 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1410560 : Path.checkChunk context decode facts instructions 1410560 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1411072 : Path.checkChunk context decode facts instructions 1411072 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1411584 : Path.checkChunk context decode facts instructions 1411584 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1412096 : Path.checkChunk context decode facts instructions 1412096 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1412608 : Path.checkChunk context decode facts instructions 1412608 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1413120 : Path.checkChunk context decode facts instructions 1413120 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1413632 : Path.checkChunk context decode facts instructions 1413632 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1414144 : Path.checkChunk context decode facts instructions 1414144 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1414656 : Path.checkChunk context decode facts instructions 1414656 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1415168 : Path.checkChunk context decode facts instructions 1415168 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1415680 : Path.checkChunk context decode facts instructions 1415680 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1416192 : Path.checkChunk context decode facts instructions 1416192 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1416704 : Path.checkChunk context decode facts instructions 1416704 512 = true := by
  decide +kernel

theorem sound_1409024 (prior : ∀ n, n < 1409024 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1417216 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1409536 := Path.chunk_sound context_valid decode facts instructions 1409024 512
    prior checked_1409024
  have h1410048 := Path.chunk_sound context_valid decode facts instructions 1409536 512
    h1409536 checked_1409536
  have h1410560 := Path.chunk_sound context_valid decode facts instructions 1410048 512
    h1410048 checked_1410048
  have h1411072 := Path.chunk_sound context_valid decode facts instructions 1410560 512
    h1410560 checked_1410560
  have h1411584 := Path.chunk_sound context_valid decode facts instructions 1411072 512
    h1411072 checked_1411072
  have h1412096 := Path.chunk_sound context_valid decode facts instructions 1411584 512
    h1411584 checked_1411584
  have h1412608 := Path.chunk_sound context_valid decode facts instructions 1412096 512
    h1412096 checked_1412096
  have h1413120 := Path.chunk_sound context_valid decode facts instructions 1412608 512
    h1412608 checked_1412608
  have h1413632 := Path.chunk_sound context_valid decode facts instructions 1413120 512
    h1413120 checked_1413120
  have h1414144 := Path.chunk_sound context_valid decode facts instructions 1413632 512
    h1413632 checked_1413632
  have h1414656 := Path.chunk_sound context_valid decode facts instructions 1414144 512
    h1414144 checked_1414144
  have h1415168 := Path.chunk_sound context_valid decode facts instructions 1414656 512
    h1414656 checked_1414656
  have h1415680 := Path.chunk_sound context_valid decode facts instructions 1415168 512
    h1415168 checked_1415168
  have h1416192 := Path.chunk_sound context_valid decode facts instructions 1415680 512
    h1415680 checked_1415680
  have h1416704 := Path.chunk_sound context_valid decode facts instructions 1416192 512
    h1416192 checked_1416192
  have h1417216 := Path.chunk_sound context_valid decode facts instructions 1416704 512
    h1416704 checked_1416704
  exact h1417216

end Sporadic.Janko3.AmalgamPresentation.Cover
