module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_614400 : Path.checkChunk context decode facts instructions 614400 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_614912 : Path.checkChunk context decode facts instructions 614912 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_615424 : Path.checkChunk context decode facts instructions 615424 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_615936 : Path.checkChunk context decode facts instructions 615936 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_616448 : Path.checkChunk context decode facts instructions 616448 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_616960 : Path.checkChunk context decode facts instructions 616960 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_617472 : Path.checkChunk context decode facts instructions 617472 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_617984 : Path.checkChunk context decode facts instructions 617984 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_618496 : Path.checkChunk context decode facts instructions 618496 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_619008 : Path.checkChunk context decode facts instructions 619008 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_619520 : Path.checkChunk context decode facts instructions 619520 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_620032 : Path.checkChunk context decode facts instructions 620032 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_620544 : Path.checkChunk context decode facts instructions 620544 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_621056 : Path.checkChunk context decode facts instructions 621056 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_621568 : Path.checkChunk context decode facts instructions 621568 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_622080 : Path.checkChunk context decode facts instructions 622080 512 = true := by
  decide +kernel

theorem sound_614400 (prior : ∀ n, n < 614400 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 622592 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h614912 := Path.chunk_sound context_valid decode facts instructions 614400 512
    prior checked_614400
  have h615424 := Path.chunk_sound context_valid decode facts instructions 614912 512
    h614912 checked_614912
  have h615936 := Path.chunk_sound context_valid decode facts instructions 615424 512
    h615424 checked_615424
  have h616448 := Path.chunk_sound context_valid decode facts instructions 615936 512
    h615936 checked_615936
  have h616960 := Path.chunk_sound context_valid decode facts instructions 616448 512
    h616448 checked_616448
  have h617472 := Path.chunk_sound context_valid decode facts instructions 616960 512
    h616960 checked_616960
  have h617984 := Path.chunk_sound context_valid decode facts instructions 617472 512
    h617472 checked_617472
  have h618496 := Path.chunk_sound context_valid decode facts instructions 617984 512
    h617984 checked_617984
  have h619008 := Path.chunk_sound context_valid decode facts instructions 618496 512
    h618496 checked_618496
  have h619520 := Path.chunk_sound context_valid decode facts instructions 619008 512
    h619008 checked_619008
  have h620032 := Path.chunk_sound context_valid decode facts instructions 619520 512
    h619520 checked_619520
  have h620544 := Path.chunk_sound context_valid decode facts instructions 620032 512
    h620032 checked_620032
  have h621056 := Path.chunk_sound context_valid decode facts instructions 620544 512
    h620544 checked_620544
  have h621568 := Path.chunk_sound context_valid decode facts instructions 621056 512
    h621056 checked_621056
  have h622080 := Path.chunk_sound context_valid decode facts instructions 621568 512
    h621568 checked_621568
  have h622592 := Path.chunk_sound context_valid decode facts instructions 622080 512
    h622080 checked_622080
  exact h622592

end Sporadic.Janko3.AmalgamPresentation.Cover
