module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_761856 : Path.checkChunk context decode facts instructions 761856 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_762368 : Path.checkChunk context decode facts instructions 762368 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_762880 : Path.checkChunk context decode facts instructions 762880 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_763392 : Path.checkChunk context decode facts instructions 763392 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_763904 : Path.checkChunk context decode facts instructions 763904 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_764416 : Path.checkChunk context decode facts instructions 764416 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_764928 : Path.checkChunk context decode facts instructions 764928 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_765440 : Path.checkChunk context decode facts instructions 765440 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_765952 : Path.checkChunk context decode facts instructions 765952 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_766464 : Path.checkChunk context decode facts instructions 766464 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_766976 : Path.checkChunk context decode facts instructions 766976 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_767488 : Path.checkChunk context decode facts instructions 767488 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_768000 : Path.checkChunk context decode facts instructions 768000 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_768512 : Path.checkChunk context decode facts instructions 768512 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_769024 : Path.checkChunk context decode facts instructions 769024 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_769536 : Path.checkChunk context decode facts instructions 769536 512 = true := by
  decide +kernel

theorem sound_761856 (prior : ∀ n, n < 761856 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 770048 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h762368 := Path.chunk_sound context_valid decode facts instructions 761856 512
    prior checked_761856
  have h762880 := Path.chunk_sound context_valid decode facts instructions 762368 512
    h762368 checked_762368
  have h763392 := Path.chunk_sound context_valid decode facts instructions 762880 512
    h762880 checked_762880
  have h763904 := Path.chunk_sound context_valid decode facts instructions 763392 512
    h763392 checked_763392
  have h764416 := Path.chunk_sound context_valid decode facts instructions 763904 512
    h763904 checked_763904
  have h764928 := Path.chunk_sound context_valid decode facts instructions 764416 512
    h764416 checked_764416
  have h765440 := Path.chunk_sound context_valid decode facts instructions 764928 512
    h764928 checked_764928
  have h765952 := Path.chunk_sound context_valid decode facts instructions 765440 512
    h765440 checked_765440
  have h766464 := Path.chunk_sound context_valid decode facts instructions 765952 512
    h765952 checked_765952
  have h766976 := Path.chunk_sound context_valid decode facts instructions 766464 512
    h766464 checked_766464
  have h767488 := Path.chunk_sound context_valid decode facts instructions 766976 512
    h766976 checked_766976
  have h768000 := Path.chunk_sound context_valid decode facts instructions 767488 512
    h767488 checked_767488
  have h768512 := Path.chunk_sound context_valid decode facts instructions 768000 512
    h768000 checked_768000
  have h769024 := Path.chunk_sound context_valid decode facts instructions 768512 512
    h768512 checked_768512
  have h769536 := Path.chunk_sound context_valid decode facts instructions 769024 512
    h769024 checked_769024
  have h770048 := Path.chunk_sound context_valid decode facts instructions 769536 512
    h769536 checked_769536
  exact h770048

end Sporadic.Janko3.AmalgamPresentation.Cover
