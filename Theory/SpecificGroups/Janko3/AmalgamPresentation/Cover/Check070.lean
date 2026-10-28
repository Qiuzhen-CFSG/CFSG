module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_573440 : Path.checkChunk context decode facts instructions 573440 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_573952 : Path.checkChunk context decode facts instructions 573952 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_574464 : Path.checkChunk context decode facts instructions 574464 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_574976 : Path.checkChunk context decode facts instructions 574976 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_575488 : Path.checkChunk context decode facts instructions 575488 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_576000 : Path.checkChunk context decode facts instructions 576000 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_576512 : Path.checkChunk context decode facts instructions 576512 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_577024 : Path.checkChunk context decode facts instructions 577024 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_577536 : Path.checkChunk context decode facts instructions 577536 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_578048 : Path.checkChunk context decode facts instructions 578048 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_578560 : Path.checkChunk context decode facts instructions 578560 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_579072 : Path.checkChunk context decode facts instructions 579072 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_579584 : Path.checkChunk context decode facts instructions 579584 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_580096 : Path.checkChunk context decode facts instructions 580096 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_580608 : Path.checkChunk context decode facts instructions 580608 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_581120 : Path.checkChunk context decode facts instructions 581120 512 = true := by
  decide +kernel

theorem sound_573440 (prior : ∀ n, n < 573440 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 581632 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h573952 := Path.chunk_sound context_valid decode facts instructions 573440 512
    prior checked_573440
  have h574464 := Path.chunk_sound context_valid decode facts instructions 573952 512
    h573952 checked_573952
  have h574976 := Path.chunk_sound context_valid decode facts instructions 574464 512
    h574464 checked_574464
  have h575488 := Path.chunk_sound context_valid decode facts instructions 574976 512
    h574976 checked_574976
  have h576000 := Path.chunk_sound context_valid decode facts instructions 575488 512
    h575488 checked_575488
  have h576512 := Path.chunk_sound context_valid decode facts instructions 576000 512
    h576000 checked_576000
  have h577024 := Path.chunk_sound context_valid decode facts instructions 576512 512
    h576512 checked_576512
  have h577536 := Path.chunk_sound context_valid decode facts instructions 577024 512
    h577024 checked_577024
  have h578048 := Path.chunk_sound context_valid decode facts instructions 577536 512
    h577536 checked_577536
  have h578560 := Path.chunk_sound context_valid decode facts instructions 578048 512
    h578048 checked_578048
  have h579072 := Path.chunk_sound context_valid decode facts instructions 578560 512
    h578560 checked_578560
  have h579584 := Path.chunk_sound context_valid decode facts instructions 579072 512
    h579072 checked_579072
  have h580096 := Path.chunk_sound context_valid decode facts instructions 579584 512
    h579584 checked_579584
  have h580608 := Path.chunk_sound context_valid decode facts instructions 580096 512
    h580096 checked_580096
  have h581120 := Path.chunk_sound context_valid decode facts instructions 580608 512
    h580608 checked_580608
  have h581632 := Path.chunk_sound context_valid decode facts instructions 581120 512
    h581120 checked_581120
  exact h581632

end Sporadic.Janko3.AmalgamPresentation.Cover
