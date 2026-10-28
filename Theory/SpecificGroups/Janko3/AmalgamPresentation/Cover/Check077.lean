module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_630784 : Path.checkChunk context decode facts instructions 630784 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_631296 : Path.checkChunk context decode facts instructions 631296 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_631808 : Path.checkChunk context decode facts instructions 631808 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_632320 : Path.checkChunk context decode facts instructions 632320 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_632832 : Path.checkChunk context decode facts instructions 632832 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_633344 : Path.checkChunk context decode facts instructions 633344 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_633856 : Path.checkChunk context decode facts instructions 633856 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_634368 : Path.checkChunk context decode facts instructions 634368 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_634880 : Path.checkChunk context decode facts instructions 634880 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_635392 : Path.checkChunk context decode facts instructions 635392 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_635904 : Path.checkChunk context decode facts instructions 635904 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_636416 : Path.checkChunk context decode facts instructions 636416 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_636928 : Path.checkChunk context decode facts instructions 636928 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_637440 : Path.checkChunk context decode facts instructions 637440 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_637952 : Path.checkChunk context decode facts instructions 637952 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_638464 : Path.checkChunk context decode facts instructions 638464 512 = true := by
  decide +kernel

theorem sound_630784 (prior : ∀ n, n < 630784 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 638976 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h631296 := Path.chunk_sound context_valid decode facts instructions 630784 512
    prior checked_630784
  have h631808 := Path.chunk_sound context_valid decode facts instructions 631296 512
    h631296 checked_631296
  have h632320 := Path.chunk_sound context_valid decode facts instructions 631808 512
    h631808 checked_631808
  have h632832 := Path.chunk_sound context_valid decode facts instructions 632320 512
    h632320 checked_632320
  have h633344 := Path.chunk_sound context_valid decode facts instructions 632832 512
    h632832 checked_632832
  have h633856 := Path.chunk_sound context_valid decode facts instructions 633344 512
    h633344 checked_633344
  have h634368 := Path.chunk_sound context_valid decode facts instructions 633856 512
    h633856 checked_633856
  have h634880 := Path.chunk_sound context_valid decode facts instructions 634368 512
    h634368 checked_634368
  have h635392 := Path.chunk_sound context_valid decode facts instructions 634880 512
    h634880 checked_634880
  have h635904 := Path.chunk_sound context_valid decode facts instructions 635392 512
    h635392 checked_635392
  have h636416 := Path.chunk_sound context_valid decode facts instructions 635904 512
    h635904 checked_635904
  have h636928 := Path.chunk_sound context_valid decode facts instructions 636416 512
    h636416 checked_636416
  have h637440 := Path.chunk_sound context_valid decode facts instructions 636928 512
    h636928 checked_636928
  have h637952 := Path.chunk_sound context_valid decode facts instructions 637440 512
    h637440 checked_637440
  have h638464 := Path.chunk_sound context_valid decode facts instructions 637952 512
    h637952 checked_637952
  have h638976 := Path.chunk_sound context_valid decode facts instructions 638464 512
    h638464 checked_638464
  exact h638976

end Sporadic.Janko3.AmalgamPresentation.Cover
