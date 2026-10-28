module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_319488 : Path.checkChunk context decode facts instructions 319488 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_320000 : Path.checkChunk context decode facts instructions 320000 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_320512 : Path.checkChunk context decode facts instructions 320512 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_321024 : Path.checkChunk context decode facts instructions 321024 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_321536 : Path.checkChunk context decode facts instructions 321536 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_322048 : Path.checkChunk context decode facts instructions 322048 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_322560 : Path.checkChunk context decode facts instructions 322560 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_323072 : Path.checkChunk context decode facts instructions 323072 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_323584 : Path.checkChunk context decode facts instructions 323584 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_324096 : Path.checkChunk context decode facts instructions 324096 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_324608 : Path.checkChunk context decode facts instructions 324608 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_325120 : Path.checkChunk context decode facts instructions 325120 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_325632 : Path.checkChunk context decode facts instructions 325632 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_326144 : Path.checkChunk context decode facts instructions 326144 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_326656 : Path.checkChunk context decode facts instructions 326656 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_327168 : Path.checkChunk context decode facts instructions 327168 512 = true := by
  decide +kernel

theorem sound_319488 (prior : ∀ n, n < 319488 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 327680 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h320000 := Path.chunk_sound context_valid decode facts instructions 319488 512
    prior checked_319488
  have h320512 := Path.chunk_sound context_valid decode facts instructions 320000 512
    h320000 checked_320000
  have h321024 := Path.chunk_sound context_valid decode facts instructions 320512 512
    h320512 checked_320512
  have h321536 := Path.chunk_sound context_valid decode facts instructions 321024 512
    h321024 checked_321024
  have h322048 := Path.chunk_sound context_valid decode facts instructions 321536 512
    h321536 checked_321536
  have h322560 := Path.chunk_sound context_valid decode facts instructions 322048 512
    h322048 checked_322048
  have h323072 := Path.chunk_sound context_valid decode facts instructions 322560 512
    h322560 checked_322560
  have h323584 := Path.chunk_sound context_valid decode facts instructions 323072 512
    h323072 checked_323072
  have h324096 := Path.chunk_sound context_valid decode facts instructions 323584 512
    h323584 checked_323584
  have h324608 := Path.chunk_sound context_valid decode facts instructions 324096 512
    h324096 checked_324096
  have h325120 := Path.chunk_sound context_valid decode facts instructions 324608 512
    h324608 checked_324608
  have h325632 := Path.chunk_sound context_valid decode facts instructions 325120 512
    h325120 checked_325120
  have h326144 := Path.chunk_sound context_valid decode facts instructions 325632 512
    h325632 checked_325632
  have h326656 := Path.chunk_sound context_valid decode facts instructions 326144 512
    h326144 checked_326144
  have h327168 := Path.chunk_sound context_valid decode facts instructions 326656 512
    h326656 checked_326656
  have h327680 := Path.chunk_sound context_valid decode facts instructions 327168 512
    h327168 checked_327168
  exact h327680

end Sporadic.Janko3.AmalgamPresentation.Cover
