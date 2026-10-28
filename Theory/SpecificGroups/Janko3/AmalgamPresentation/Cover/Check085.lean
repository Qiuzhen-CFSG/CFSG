module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_696320 : Path.checkChunk context decode facts instructions 696320 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_696832 : Path.checkChunk context decode facts instructions 696832 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_697344 : Path.checkChunk context decode facts instructions 697344 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_697856 : Path.checkChunk context decode facts instructions 697856 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_698368 : Path.checkChunk context decode facts instructions 698368 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_698880 : Path.checkChunk context decode facts instructions 698880 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_699392 : Path.checkChunk context decode facts instructions 699392 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_699904 : Path.checkChunk context decode facts instructions 699904 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_700416 : Path.checkChunk context decode facts instructions 700416 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_700928 : Path.checkChunk context decode facts instructions 700928 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_701440 : Path.checkChunk context decode facts instructions 701440 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_701952 : Path.checkChunk context decode facts instructions 701952 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_702464 : Path.checkChunk context decode facts instructions 702464 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_702976 : Path.checkChunk context decode facts instructions 702976 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_703488 : Path.checkChunk context decode facts instructions 703488 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_704000 : Path.checkChunk context decode facts instructions 704000 512 = true := by
  decide +kernel

theorem sound_696320 (prior : ∀ n, n < 696320 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 704512 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h696832 := Path.chunk_sound context_valid decode facts instructions 696320 512
    prior checked_696320
  have h697344 := Path.chunk_sound context_valid decode facts instructions 696832 512
    h696832 checked_696832
  have h697856 := Path.chunk_sound context_valid decode facts instructions 697344 512
    h697344 checked_697344
  have h698368 := Path.chunk_sound context_valid decode facts instructions 697856 512
    h697856 checked_697856
  have h698880 := Path.chunk_sound context_valid decode facts instructions 698368 512
    h698368 checked_698368
  have h699392 := Path.chunk_sound context_valid decode facts instructions 698880 512
    h698880 checked_698880
  have h699904 := Path.chunk_sound context_valid decode facts instructions 699392 512
    h699392 checked_699392
  have h700416 := Path.chunk_sound context_valid decode facts instructions 699904 512
    h699904 checked_699904
  have h700928 := Path.chunk_sound context_valid decode facts instructions 700416 512
    h700416 checked_700416
  have h701440 := Path.chunk_sound context_valid decode facts instructions 700928 512
    h700928 checked_700928
  have h701952 := Path.chunk_sound context_valid decode facts instructions 701440 512
    h701440 checked_701440
  have h702464 := Path.chunk_sound context_valid decode facts instructions 701952 512
    h701952 checked_701952
  have h702976 := Path.chunk_sound context_valid decode facts instructions 702464 512
    h702464 checked_702464
  have h703488 := Path.chunk_sound context_valid decode facts instructions 702976 512
    h702976 checked_702976
  have h704000 := Path.chunk_sound context_valid decode facts instructions 703488 512
    h703488 checked_703488
  have h704512 := Path.chunk_sound context_valid decode facts instructions 704000 512
    h704000 checked_704000
  exact h704512

end Sporadic.Janko3.AmalgamPresentation.Cover
