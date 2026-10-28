module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1458176 : Path.checkChunk context decode facts instructions 1458176 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1458688 : Path.checkChunk context decode facts instructions 1458688 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1459200 : Path.checkChunk context decode facts instructions 1459200 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1459712 : Path.checkChunk context decode facts instructions 1459712 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1460224 : Path.checkChunk context decode facts instructions 1460224 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1460736 : Path.checkChunk context decode facts instructions 1460736 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1461248 : Path.checkChunk context decode facts instructions 1461248 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1461760 : Path.checkChunk context decode facts instructions 1461760 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1462272 : Path.checkChunk context decode facts instructions 1462272 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1462784 : Path.checkChunk context decode facts instructions 1462784 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1463296 : Path.checkChunk context decode facts instructions 1463296 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1463808 : Path.checkChunk context decode facts instructions 1463808 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1464320 : Path.checkChunk context decode facts instructions 1464320 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1464832 : Path.checkChunk context decode facts instructions 1464832 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1465344 : Path.checkChunk context decode facts instructions 1465344 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1465856 : Path.checkChunk context decode facts instructions 1465856 512 = true := by
  decide +kernel

theorem sound_1458176 (prior : ∀ n, n < 1458176 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1466368 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1458688 := Path.chunk_sound context_valid decode facts instructions 1458176 512
    prior checked_1458176
  have h1459200 := Path.chunk_sound context_valid decode facts instructions 1458688 512
    h1458688 checked_1458688
  have h1459712 := Path.chunk_sound context_valid decode facts instructions 1459200 512
    h1459200 checked_1459200
  have h1460224 := Path.chunk_sound context_valid decode facts instructions 1459712 512
    h1459712 checked_1459712
  have h1460736 := Path.chunk_sound context_valid decode facts instructions 1460224 512
    h1460224 checked_1460224
  have h1461248 := Path.chunk_sound context_valid decode facts instructions 1460736 512
    h1460736 checked_1460736
  have h1461760 := Path.chunk_sound context_valid decode facts instructions 1461248 512
    h1461248 checked_1461248
  have h1462272 := Path.chunk_sound context_valid decode facts instructions 1461760 512
    h1461760 checked_1461760
  have h1462784 := Path.chunk_sound context_valid decode facts instructions 1462272 512
    h1462272 checked_1462272
  have h1463296 := Path.chunk_sound context_valid decode facts instructions 1462784 512
    h1462784 checked_1462784
  have h1463808 := Path.chunk_sound context_valid decode facts instructions 1463296 512
    h1463296 checked_1463296
  have h1464320 := Path.chunk_sound context_valid decode facts instructions 1463808 512
    h1463808 checked_1463808
  have h1464832 := Path.chunk_sound context_valid decode facts instructions 1464320 512
    h1464320 checked_1464320
  have h1465344 := Path.chunk_sound context_valid decode facts instructions 1464832 512
    h1464832 checked_1464832
  have h1465856 := Path.chunk_sound context_valid decode facts instructions 1465344 512
    h1465344 checked_1465344
  have h1466368 := Path.chunk_sound context_valid decode facts instructions 1465856 512
    h1465856 checked_1465856
  exact h1466368

end Sporadic.Janko3.AmalgamPresentation.Cover
