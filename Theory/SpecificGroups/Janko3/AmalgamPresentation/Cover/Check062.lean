module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_507904 : Path.checkChunk context decode facts instructions 507904 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_508416 : Path.checkChunk context decode facts instructions 508416 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_508928 : Path.checkChunk context decode facts instructions 508928 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_509440 : Path.checkChunk context decode facts instructions 509440 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_509952 : Path.checkChunk context decode facts instructions 509952 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_510464 : Path.checkChunk context decode facts instructions 510464 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_510976 : Path.checkChunk context decode facts instructions 510976 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_511488 : Path.checkChunk context decode facts instructions 511488 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_512000 : Path.checkChunk context decode facts instructions 512000 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_512512 : Path.checkChunk context decode facts instructions 512512 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_513024 : Path.checkChunk context decode facts instructions 513024 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_513536 : Path.checkChunk context decode facts instructions 513536 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_514048 : Path.checkChunk context decode facts instructions 514048 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_514560 : Path.checkChunk context decode facts instructions 514560 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_515072 : Path.checkChunk context decode facts instructions 515072 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_515584 : Path.checkChunk context decode facts instructions 515584 512 = true := by
  decide +kernel

theorem sound_507904 (prior : ∀ n, n < 507904 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 516096 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h508416 := Path.chunk_sound context_valid decode facts instructions 507904 512
    prior checked_507904
  have h508928 := Path.chunk_sound context_valid decode facts instructions 508416 512
    h508416 checked_508416
  have h509440 := Path.chunk_sound context_valid decode facts instructions 508928 512
    h508928 checked_508928
  have h509952 := Path.chunk_sound context_valid decode facts instructions 509440 512
    h509440 checked_509440
  have h510464 := Path.chunk_sound context_valid decode facts instructions 509952 512
    h509952 checked_509952
  have h510976 := Path.chunk_sound context_valid decode facts instructions 510464 512
    h510464 checked_510464
  have h511488 := Path.chunk_sound context_valid decode facts instructions 510976 512
    h510976 checked_510976
  have h512000 := Path.chunk_sound context_valid decode facts instructions 511488 512
    h511488 checked_511488
  have h512512 := Path.chunk_sound context_valid decode facts instructions 512000 512
    h512000 checked_512000
  have h513024 := Path.chunk_sound context_valid decode facts instructions 512512 512
    h512512 checked_512512
  have h513536 := Path.chunk_sound context_valid decode facts instructions 513024 512
    h513024 checked_513024
  have h514048 := Path.chunk_sound context_valid decode facts instructions 513536 512
    h513536 checked_513536
  have h514560 := Path.chunk_sound context_valid decode facts instructions 514048 512
    h514048 checked_514048
  have h515072 := Path.chunk_sound context_valid decode facts instructions 514560 512
    h514560 checked_514560
  have h515584 := Path.chunk_sound context_valid decode facts instructions 515072 512
    h515072 checked_515072
  have h516096 := Path.chunk_sound context_valid decode facts instructions 515584 512
    h515584 checked_515584
  exact h516096

end Sporadic.Janko3.AmalgamPresentation.Cover
