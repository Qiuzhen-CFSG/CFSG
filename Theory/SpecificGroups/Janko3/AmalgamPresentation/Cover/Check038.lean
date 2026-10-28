module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_311296 : Path.checkChunk context decode facts instructions 311296 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_311808 : Path.checkChunk context decode facts instructions 311808 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_312320 : Path.checkChunk context decode facts instructions 312320 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_312832 : Path.checkChunk context decode facts instructions 312832 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_313344 : Path.checkChunk context decode facts instructions 313344 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_313856 : Path.checkChunk context decode facts instructions 313856 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_314368 : Path.checkChunk context decode facts instructions 314368 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_314880 : Path.checkChunk context decode facts instructions 314880 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_315392 : Path.checkChunk context decode facts instructions 315392 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_315904 : Path.checkChunk context decode facts instructions 315904 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_316416 : Path.checkChunk context decode facts instructions 316416 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_316928 : Path.checkChunk context decode facts instructions 316928 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_317440 : Path.checkChunk context decode facts instructions 317440 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_317952 : Path.checkChunk context decode facts instructions 317952 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_318464 : Path.checkChunk context decode facts instructions 318464 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_318976 : Path.checkChunk context decode facts instructions 318976 512 = true := by
  decide +kernel

theorem sound_311296 (prior : ∀ n, n < 311296 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 319488 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h311808 := Path.chunk_sound context_valid decode facts instructions 311296 512
    prior checked_311296
  have h312320 := Path.chunk_sound context_valid decode facts instructions 311808 512
    h311808 checked_311808
  have h312832 := Path.chunk_sound context_valid decode facts instructions 312320 512
    h312320 checked_312320
  have h313344 := Path.chunk_sound context_valid decode facts instructions 312832 512
    h312832 checked_312832
  have h313856 := Path.chunk_sound context_valid decode facts instructions 313344 512
    h313344 checked_313344
  have h314368 := Path.chunk_sound context_valid decode facts instructions 313856 512
    h313856 checked_313856
  have h314880 := Path.chunk_sound context_valid decode facts instructions 314368 512
    h314368 checked_314368
  have h315392 := Path.chunk_sound context_valid decode facts instructions 314880 512
    h314880 checked_314880
  have h315904 := Path.chunk_sound context_valid decode facts instructions 315392 512
    h315392 checked_315392
  have h316416 := Path.chunk_sound context_valid decode facts instructions 315904 512
    h315904 checked_315904
  have h316928 := Path.chunk_sound context_valid decode facts instructions 316416 512
    h316416 checked_316416
  have h317440 := Path.chunk_sound context_valid decode facts instructions 316928 512
    h316928 checked_316928
  have h317952 := Path.chunk_sound context_valid decode facts instructions 317440 512
    h317440 checked_317440
  have h318464 := Path.chunk_sound context_valid decode facts instructions 317952 512
    h317952 checked_317952
  have h318976 := Path.chunk_sound context_valid decode facts instructions 318464 512
    h318464 checked_318464
  have h319488 := Path.chunk_sound context_valid decode facts instructions 318976 512
    h318976 checked_318976
  exact h319488

end Sporadic.Janko3.AmalgamPresentation.Cover
