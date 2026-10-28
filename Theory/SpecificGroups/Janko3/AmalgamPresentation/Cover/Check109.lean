module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_892928 : Path.checkChunk context decode facts instructions 892928 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_893440 : Path.checkChunk context decode facts instructions 893440 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_893952 : Path.checkChunk context decode facts instructions 893952 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_894464 : Path.checkChunk context decode facts instructions 894464 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_894976 : Path.checkChunk context decode facts instructions 894976 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_895488 : Path.checkChunk context decode facts instructions 895488 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_896000 : Path.checkChunk context decode facts instructions 896000 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_896512 : Path.checkChunk context decode facts instructions 896512 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_897024 : Path.checkChunk context decode facts instructions 897024 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_897536 : Path.checkChunk context decode facts instructions 897536 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_898048 : Path.checkChunk context decode facts instructions 898048 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_898560 : Path.checkChunk context decode facts instructions 898560 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_899072 : Path.checkChunk context decode facts instructions 899072 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_899584 : Path.checkChunk context decode facts instructions 899584 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_900096 : Path.checkChunk context decode facts instructions 900096 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_900608 : Path.checkChunk context decode facts instructions 900608 512 = true := by
  decide +kernel

theorem sound_892928 (prior : ∀ n, n < 892928 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 901120 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h893440 := Path.chunk_sound context_valid decode facts instructions 892928 512
    prior checked_892928
  have h893952 := Path.chunk_sound context_valid decode facts instructions 893440 512
    h893440 checked_893440
  have h894464 := Path.chunk_sound context_valid decode facts instructions 893952 512
    h893952 checked_893952
  have h894976 := Path.chunk_sound context_valid decode facts instructions 894464 512
    h894464 checked_894464
  have h895488 := Path.chunk_sound context_valid decode facts instructions 894976 512
    h894976 checked_894976
  have h896000 := Path.chunk_sound context_valid decode facts instructions 895488 512
    h895488 checked_895488
  have h896512 := Path.chunk_sound context_valid decode facts instructions 896000 512
    h896000 checked_896000
  have h897024 := Path.chunk_sound context_valid decode facts instructions 896512 512
    h896512 checked_896512
  have h897536 := Path.chunk_sound context_valid decode facts instructions 897024 512
    h897024 checked_897024
  have h898048 := Path.chunk_sound context_valid decode facts instructions 897536 512
    h897536 checked_897536
  have h898560 := Path.chunk_sound context_valid decode facts instructions 898048 512
    h898048 checked_898048
  have h899072 := Path.chunk_sound context_valid decode facts instructions 898560 512
    h898560 checked_898560
  have h899584 := Path.chunk_sound context_valid decode facts instructions 899072 512
    h899072 checked_899072
  have h900096 := Path.chunk_sound context_valid decode facts instructions 899584 512
    h899584 checked_899584
  have h900608 := Path.chunk_sound context_valid decode facts instructions 900096 512
    h900096 checked_900096
  have h901120 := Path.chunk_sound context_valid decode facts instructions 900608 512
    h900608 checked_900608
  exact h901120

end Sporadic.Janko3.AmalgamPresentation.Cover
