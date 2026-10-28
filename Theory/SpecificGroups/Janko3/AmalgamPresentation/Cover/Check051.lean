module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_417792 : Path.checkChunk context decode facts instructions 417792 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_418304 : Path.checkChunk context decode facts instructions 418304 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_418816 : Path.checkChunk context decode facts instructions 418816 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_419328 : Path.checkChunk context decode facts instructions 419328 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_419840 : Path.checkChunk context decode facts instructions 419840 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_420352 : Path.checkChunk context decode facts instructions 420352 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_420864 : Path.checkChunk context decode facts instructions 420864 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_421376 : Path.checkChunk context decode facts instructions 421376 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_421888 : Path.checkChunk context decode facts instructions 421888 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_422400 : Path.checkChunk context decode facts instructions 422400 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_422912 : Path.checkChunk context decode facts instructions 422912 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_423424 : Path.checkChunk context decode facts instructions 423424 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_423936 : Path.checkChunk context decode facts instructions 423936 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_424448 : Path.checkChunk context decode facts instructions 424448 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_424960 : Path.checkChunk context decode facts instructions 424960 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_425472 : Path.checkChunk context decode facts instructions 425472 512 = true := by
  decide +kernel

theorem sound_417792 (prior : ∀ n, n < 417792 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 425984 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h418304 := Path.chunk_sound context_valid decode facts instructions 417792 512
    prior checked_417792
  have h418816 := Path.chunk_sound context_valid decode facts instructions 418304 512
    h418304 checked_418304
  have h419328 := Path.chunk_sound context_valid decode facts instructions 418816 512
    h418816 checked_418816
  have h419840 := Path.chunk_sound context_valid decode facts instructions 419328 512
    h419328 checked_419328
  have h420352 := Path.chunk_sound context_valid decode facts instructions 419840 512
    h419840 checked_419840
  have h420864 := Path.chunk_sound context_valid decode facts instructions 420352 512
    h420352 checked_420352
  have h421376 := Path.chunk_sound context_valid decode facts instructions 420864 512
    h420864 checked_420864
  have h421888 := Path.chunk_sound context_valid decode facts instructions 421376 512
    h421376 checked_421376
  have h422400 := Path.chunk_sound context_valid decode facts instructions 421888 512
    h421888 checked_421888
  have h422912 := Path.chunk_sound context_valid decode facts instructions 422400 512
    h422400 checked_422400
  have h423424 := Path.chunk_sound context_valid decode facts instructions 422912 512
    h422912 checked_422912
  have h423936 := Path.chunk_sound context_valid decode facts instructions 423424 512
    h423424 checked_423424
  have h424448 := Path.chunk_sound context_valid decode facts instructions 423936 512
    h423936 checked_423936
  have h424960 := Path.chunk_sound context_valid decode facts instructions 424448 512
    h424448 checked_424448
  have h425472 := Path.chunk_sound context_valid decode facts instructions 424960 512
    h424960 checked_424960
  have h425984 := Path.chunk_sound context_valid decode facts instructions 425472 512
    h425472 checked_425472
  exact h425984

end Sporadic.Janko3.AmalgamPresentation.Cover
