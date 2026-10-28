module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1466368 : Path.checkChunk context decode facts instructions 1466368 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1466880 : Path.checkChunk context decode facts instructions 1466880 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1467392 : Path.checkChunk context decode facts instructions 1467392 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1467904 : Path.checkChunk context decode facts instructions 1467904 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1468416 : Path.checkChunk context decode facts instructions 1468416 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1468928 : Path.checkChunk context decode facts instructions 1468928 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1469440 : Path.checkChunk context decode facts instructions 1469440 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1469952 : Path.checkChunk context decode facts instructions 1469952 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1470464 : Path.checkChunk context decode facts instructions 1470464 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1470976 : Path.checkChunk context decode facts instructions 1470976 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1471488 : Path.checkChunk context decode facts instructions 1471488 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1472000 : Path.checkChunk context decode facts instructions 1472000 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1472512 : Path.checkChunk context decode facts instructions 1472512 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1473024 : Path.checkChunk context decode facts instructions 1473024 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1473536 : Path.checkChunk context decode facts instructions 1473536 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1474048 : Path.checkChunk context decode facts instructions 1474048 512 = true := by
  decide +kernel

theorem sound_1466368 (prior : ∀ n, n < 1466368 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1474560 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1466880 := Path.chunk_sound context_valid decode facts instructions 1466368 512
    prior checked_1466368
  have h1467392 := Path.chunk_sound context_valid decode facts instructions 1466880 512
    h1466880 checked_1466880
  have h1467904 := Path.chunk_sound context_valid decode facts instructions 1467392 512
    h1467392 checked_1467392
  have h1468416 := Path.chunk_sound context_valid decode facts instructions 1467904 512
    h1467904 checked_1467904
  have h1468928 := Path.chunk_sound context_valid decode facts instructions 1468416 512
    h1468416 checked_1468416
  have h1469440 := Path.chunk_sound context_valid decode facts instructions 1468928 512
    h1468928 checked_1468928
  have h1469952 := Path.chunk_sound context_valid decode facts instructions 1469440 512
    h1469440 checked_1469440
  have h1470464 := Path.chunk_sound context_valid decode facts instructions 1469952 512
    h1469952 checked_1469952
  have h1470976 := Path.chunk_sound context_valid decode facts instructions 1470464 512
    h1470464 checked_1470464
  have h1471488 := Path.chunk_sound context_valid decode facts instructions 1470976 512
    h1470976 checked_1470976
  have h1472000 := Path.chunk_sound context_valid decode facts instructions 1471488 512
    h1471488 checked_1471488
  have h1472512 := Path.chunk_sound context_valid decode facts instructions 1472000 512
    h1472000 checked_1472000
  have h1473024 := Path.chunk_sound context_valid decode facts instructions 1472512 512
    h1472512 checked_1472512
  have h1473536 := Path.chunk_sound context_valid decode facts instructions 1473024 512
    h1473024 checked_1473024
  have h1474048 := Path.chunk_sound context_valid decode facts instructions 1473536 512
    h1473536 checked_1473536
  have h1474560 := Path.chunk_sound context_valid decode facts instructions 1474048 512
    h1474048 checked_1474048
  exact h1474560

end Sporadic.Janko3.AmalgamPresentation.Cover
