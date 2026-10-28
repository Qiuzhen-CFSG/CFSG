module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_335872 : Path.checkChunk context decode facts instructions 335872 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_336384 : Path.checkChunk context decode facts instructions 336384 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_336896 : Path.checkChunk context decode facts instructions 336896 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_337408 : Path.checkChunk context decode facts instructions 337408 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_337920 : Path.checkChunk context decode facts instructions 337920 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_338432 : Path.checkChunk context decode facts instructions 338432 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_338944 : Path.checkChunk context decode facts instructions 338944 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_339456 : Path.checkChunk context decode facts instructions 339456 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_339968 : Path.checkChunk context decode facts instructions 339968 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_340480 : Path.checkChunk context decode facts instructions 340480 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_340992 : Path.checkChunk context decode facts instructions 340992 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_341504 : Path.checkChunk context decode facts instructions 341504 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_342016 : Path.checkChunk context decode facts instructions 342016 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_342528 : Path.checkChunk context decode facts instructions 342528 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_343040 : Path.checkChunk context decode facts instructions 343040 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_343552 : Path.checkChunk context decode facts instructions 343552 512 = true := by
  decide +kernel

theorem sound_335872 (prior : ∀ n, n < 335872 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 344064 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h336384 := Path.chunk_sound context_valid decode facts instructions 335872 512
    prior checked_335872
  have h336896 := Path.chunk_sound context_valid decode facts instructions 336384 512
    h336384 checked_336384
  have h337408 := Path.chunk_sound context_valid decode facts instructions 336896 512
    h336896 checked_336896
  have h337920 := Path.chunk_sound context_valid decode facts instructions 337408 512
    h337408 checked_337408
  have h338432 := Path.chunk_sound context_valid decode facts instructions 337920 512
    h337920 checked_337920
  have h338944 := Path.chunk_sound context_valid decode facts instructions 338432 512
    h338432 checked_338432
  have h339456 := Path.chunk_sound context_valid decode facts instructions 338944 512
    h338944 checked_338944
  have h339968 := Path.chunk_sound context_valid decode facts instructions 339456 512
    h339456 checked_339456
  have h340480 := Path.chunk_sound context_valid decode facts instructions 339968 512
    h339968 checked_339968
  have h340992 := Path.chunk_sound context_valid decode facts instructions 340480 512
    h340480 checked_340480
  have h341504 := Path.chunk_sound context_valid decode facts instructions 340992 512
    h340992 checked_340992
  have h342016 := Path.chunk_sound context_valid decode facts instructions 341504 512
    h341504 checked_341504
  have h342528 := Path.chunk_sound context_valid decode facts instructions 342016 512
    h342016 checked_342016
  have h343040 := Path.chunk_sound context_valid decode facts instructions 342528 512
    h342528 checked_342528
  have h343552 := Path.chunk_sound context_valid decode facts instructions 343040 512
    h343040 checked_343040
  have h344064 := Path.chunk_sound context_valid decode facts instructions 343552 512
    h343552 checked_343552
  exact h344064

end Sporadic.Janko3.AmalgamPresentation.Cover
