module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_999424 : Path.checkChunk context decode facts instructions 999424 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_999936 : Path.checkChunk context decode facts instructions 999936 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1000448 : Path.checkChunk context decode facts instructions 1000448 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1000960 : Path.checkChunk context decode facts instructions 1000960 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1001472 : Path.checkChunk context decode facts instructions 1001472 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1001984 : Path.checkChunk context decode facts instructions 1001984 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1002496 : Path.checkChunk context decode facts instructions 1002496 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1003008 : Path.checkChunk context decode facts instructions 1003008 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1003520 : Path.checkChunk context decode facts instructions 1003520 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1004032 : Path.checkChunk context decode facts instructions 1004032 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1004544 : Path.checkChunk context decode facts instructions 1004544 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1005056 : Path.checkChunk context decode facts instructions 1005056 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1005568 : Path.checkChunk context decode facts instructions 1005568 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1006080 : Path.checkChunk context decode facts instructions 1006080 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1006592 : Path.checkChunk context decode facts instructions 1006592 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1007104 : Path.checkChunk context decode facts instructions 1007104 512 = true := by
  decide +kernel

theorem sound_999424 (prior : ∀ n, n < 999424 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1007616 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h999936 := Path.chunk_sound context_valid decode facts instructions 999424 512
    prior checked_999424
  have h1000448 := Path.chunk_sound context_valid decode facts instructions 999936 512
    h999936 checked_999936
  have h1000960 := Path.chunk_sound context_valid decode facts instructions 1000448 512
    h1000448 checked_1000448
  have h1001472 := Path.chunk_sound context_valid decode facts instructions 1000960 512
    h1000960 checked_1000960
  have h1001984 := Path.chunk_sound context_valid decode facts instructions 1001472 512
    h1001472 checked_1001472
  have h1002496 := Path.chunk_sound context_valid decode facts instructions 1001984 512
    h1001984 checked_1001984
  have h1003008 := Path.chunk_sound context_valid decode facts instructions 1002496 512
    h1002496 checked_1002496
  have h1003520 := Path.chunk_sound context_valid decode facts instructions 1003008 512
    h1003008 checked_1003008
  have h1004032 := Path.chunk_sound context_valid decode facts instructions 1003520 512
    h1003520 checked_1003520
  have h1004544 := Path.chunk_sound context_valid decode facts instructions 1004032 512
    h1004032 checked_1004032
  have h1005056 := Path.chunk_sound context_valid decode facts instructions 1004544 512
    h1004544 checked_1004544
  have h1005568 := Path.chunk_sound context_valid decode facts instructions 1005056 512
    h1005056 checked_1005056
  have h1006080 := Path.chunk_sound context_valid decode facts instructions 1005568 512
    h1005568 checked_1005568
  have h1006592 := Path.chunk_sound context_valid decode facts instructions 1006080 512
    h1006080 checked_1006080
  have h1007104 := Path.chunk_sound context_valid decode facts instructions 1006592 512
    h1006592 checked_1006592
  have h1007616 := Path.chunk_sound context_valid decode facts instructions 1007104 512
    h1007104 checked_1007104
  exact h1007616

end Sporadic.Janko3.AmalgamPresentation.Cover
