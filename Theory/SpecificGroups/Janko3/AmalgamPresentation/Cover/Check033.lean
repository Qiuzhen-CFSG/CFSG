module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_270336 : Path.checkChunk context decode facts instructions 270336 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_270848 : Path.checkChunk context decode facts instructions 270848 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_271360 : Path.checkChunk context decode facts instructions 271360 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_271872 : Path.checkChunk context decode facts instructions 271872 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_272384 : Path.checkChunk context decode facts instructions 272384 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_272896 : Path.checkChunk context decode facts instructions 272896 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_273408 : Path.checkChunk context decode facts instructions 273408 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_273920 : Path.checkChunk context decode facts instructions 273920 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_274432 : Path.checkChunk context decode facts instructions 274432 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_274944 : Path.checkChunk context decode facts instructions 274944 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_275456 : Path.checkChunk context decode facts instructions 275456 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_275968 : Path.checkChunk context decode facts instructions 275968 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_276480 : Path.checkChunk context decode facts instructions 276480 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_276992 : Path.checkChunk context decode facts instructions 276992 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_277504 : Path.checkChunk context decode facts instructions 277504 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_278016 : Path.checkChunk context decode facts instructions 278016 512 = true := by
  decide +kernel

theorem sound_270336 (prior : ∀ n, n < 270336 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 278528 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h270848 := Path.chunk_sound context_valid decode facts instructions 270336 512
    prior checked_270336
  have h271360 := Path.chunk_sound context_valid decode facts instructions 270848 512
    h270848 checked_270848
  have h271872 := Path.chunk_sound context_valid decode facts instructions 271360 512
    h271360 checked_271360
  have h272384 := Path.chunk_sound context_valid decode facts instructions 271872 512
    h271872 checked_271872
  have h272896 := Path.chunk_sound context_valid decode facts instructions 272384 512
    h272384 checked_272384
  have h273408 := Path.chunk_sound context_valid decode facts instructions 272896 512
    h272896 checked_272896
  have h273920 := Path.chunk_sound context_valid decode facts instructions 273408 512
    h273408 checked_273408
  have h274432 := Path.chunk_sound context_valid decode facts instructions 273920 512
    h273920 checked_273920
  have h274944 := Path.chunk_sound context_valid decode facts instructions 274432 512
    h274432 checked_274432
  have h275456 := Path.chunk_sound context_valid decode facts instructions 274944 512
    h274944 checked_274944
  have h275968 := Path.chunk_sound context_valid decode facts instructions 275456 512
    h275456 checked_275456
  have h276480 := Path.chunk_sound context_valid decode facts instructions 275968 512
    h275968 checked_275968
  have h276992 := Path.chunk_sound context_valid decode facts instructions 276480 512
    h276480 checked_276480
  have h277504 := Path.chunk_sound context_valid decode facts instructions 276992 512
    h276992 checked_276992
  have h278016 := Path.chunk_sound context_valid decode facts instructions 277504 512
    h277504 checked_277504
  have h278528 := Path.chunk_sound context_valid decode facts instructions 278016 512
    h278016 checked_278016
  exact h278528

end Sporadic.Janko3.AmalgamPresentation.Cover
