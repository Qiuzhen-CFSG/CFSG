module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_442368 : Path.checkChunk context decode facts instructions 442368 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_442880 : Path.checkChunk context decode facts instructions 442880 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_443392 : Path.checkChunk context decode facts instructions 443392 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_443904 : Path.checkChunk context decode facts instructions 443904 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_444416 : Path.checkChunk context decode facts instructions 444416 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_444928 : Path.checkChunk context decode facts instructions 444928 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_445440 : Path.checkChunk context decode facts instructions 445440 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_445952 : Path.checkChunk context decode facts instructions 445952 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_446464 : Path.checkChunk context decode facts instructions 446464 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_446976 : Path.checkChunk context decode facts instructions 446976 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_447488 : Path.checkChunk context decode facts instructions 447488 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_448000 : Path.checkChunk context decode facts instructions 448000 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_448512 : Path.checkChunk context decode facts instructions 448512 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_449024 : Path.checkChunk context decode facts instructions 449024 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_449536 : Path.checkChunk context decode facts instructions 449536 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_450048 : Path.checkChunk context decode facts instructions 450048 512 = true := by
  decide +kernel

theorem sound_442368 (prior : ∀ n, n < 442368 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 450560 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h442880 := Path.chunk_sound context_valid decode facts instructions 442368 512
    prior checked_442368
  have h443392 := Path.chunk_sound context_valid decode facts instructions 442880 512
    h442880 checked_442880
  have h443904 := Path.chunk_sound context_valid decode facts instructions 443392 512
    h443392 checked_443392
  have h444416 := Path.chunk_sound context_valid decode facts instructions 443904 512
    h443904 checked_443904
  have h444928 := Path.chunk_sound context_valid decode facts instructions 444416 512
    h444416 checked_444416
  have h445440 := Path.chunk_sound context_valid decode facts instructions 444928 512
    h444928 checked_444928
  have h445952 := Path.chunk_sound context_valid decode facts instructions 445440 512
    h445440 checked_445440
  have h446464 := Path.chunk_sound context_valid decode facts instructions 445952 512
    h445952 checked_445952
  have h446976 := Path.chunk_sound context_valid decode facts instructions 446464 512
    h446464 checked_446464
  have h447488 := Path.chunk_sound context_valid decode facts instructions 446976 512
    h446976 checked_446976
  have h448000 := Path.chunk_sound context_valid decode facts instructions 447488 512
    h447488 checked_447488
  have h448512 := Path.chunk_sound context_valid decode facts instructions 448000 512
    h448000 checked_448000
  have h449024 := Path.chunk_sound context_valid decode facts instructions 448512 512
    h448512 checked_448512
  have h449536 := Path.chunk_sound context_valid decode facts instructions 449024 512
    h449024 checked_449024
  have h450048 := Path.chunk_sound context_valid decode facts instructions 449536 512
    h449536 checked_449536
  have h450560 := Path.chunk_sound context_valid decode facts instructions 450048 512
    h450048 checked_450048
  exact h450560

end Sporadic.Janko3.AmalgamPresentation.Cover
