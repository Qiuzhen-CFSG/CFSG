module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_483328 : Path.checkChunk context decode facts instructions 483328 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_483840 : Path.checkChunk context decode facts instructions 483840 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_484352 : Path.checkChunk context decode facts instructions 484352 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_484864 : Path.checkChunk context decode facts instructions 484864 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_485376 : Path.checkChunk context decode facts instructions 485376 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_485888 : Path.checkChunk context decode facts instructions 485888 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_486400 : Path.checkChunk context decode facts instructions 486400 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_486912 : Path.checkChunk context decode facts instructions 486912 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_487424 : Path.checkChunk context decode facts instructions 487424 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_487936 : Path.checkChunk context decode facts instructions 487936 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_488448 : Path.checkChunk context decode facts instructions 488448 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_488960 : Path.checkChunk context decode facts instructions 488960 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_489472 : Path.checkChunk context decode facts instructions 489472 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_489984 : Path.checkChunk context decode facts instructions 489984 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_490496 : Path.checkChunk context decode facts instructions 490496 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_491008 : Path.checkChunk context decode facts instructions 491008 512 = true := by
  decide +kernel

theorem sound_483328 (prior : ∀ n, n < 483328 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 491520 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h483840 := Path.chunk_sound context_valid decode facts instructions 483328 512
    prior checked_483328
  have h484352 := Path.chunk_sound context_valid decode facts instructions 483840 512
    h483840 checked_483840
  have h484864 := Path.chunk_sound context_valid decode facts instructions 484352 512
    h484352 checked_484352
  have h485376 := Path.chunk_sound context_valid decode facts instructions 484864 512
    h484864 checked_484864
  have h485888 := Path.chunk_sound context_valid decode facts instructions 485376 512
    h485376 checked_485376
  have h486400 := Path.chunk_sound context_valid decode facts instructions 485888 512
    h485888 checked_485888
  have h486912 := Path.chunk_sound context_valid decode facts instructions 486400 512
    h486400 checked_486400
  have h487424 := Path.chunk_sound context_valid decode facts instructions 486912 512
    h486912 checked_486912
  have h487936 := Path.chunk_sound context_valid decode facts instructions 487424 512
    h487424 checked_487424
  have h488448 := Path.chunk_sound context_valid decode facts instructions 487936 512
    h487936 checked_487936
  have h488960 := Path.chunk_sound context_valid decode facts instructions 488448 512
    h488448 checked_488448
  have h489472 := Path.chunk_sound context_valid decode facts instructions 488960 512
    h488960 checked_488960
  have h489984 := Path.chunk_sound context_valid decode facts instructions 489472 512
    h489472 checked_489472
  have h490496 := Path.chunk_sound context_valid decode facts instructions 489984 512
    h489984 checked_489984
  have h491008 := Path.chunk_sound context_valid decode facts instructions 490496 512
    h490496 checked_490496
  have h491520 := Path.chunk_sound context_valid decode facts instructions 491008 512
    h491008 checked_491008
  exact h491520

end Sporadic.Janko3.AmalgamPresentation.Cover
