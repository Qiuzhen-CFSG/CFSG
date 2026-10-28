module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_425984 : Path.checkChunk context decode facts instructions 425984 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_426496 : Path.checkChunk context decode facts instructions 426496 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_427008 : Path.checkChunk context decode facts instructions 427008 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_427520 : Path.checkChunk context decode facts instructions 427520 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_428032 : Path.checkChunk context decode facts instructions 428032 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_428544 : Path.checkChunk context decode facts instructions 428544 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_429056 : Path.checkChunk context decode facts instructions 429056 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_429568 : Path.checkChunk context decode facts instructions 429568 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_430080 : Path.checkChunk context decode facts instructions 430080 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_430592 : Path.checkChunk context decode facts instructions 430592 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_431104 : Path.checkChunk context decode facts instructions 431104 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_431616 : Path.checkChunk context decode facts instructions 431616 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_432128 : Path.checkChunk context decode facts instructions 432128 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_432640 : Path.checkChunk context decode facts instructions 432640 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_433152 : Path.checkChunk context decode facts instructions 433152 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_433664 : Path.checkChunk context decode facts instructions 433664 512 = true := by
  decide +kernel

theorem sound_425984 (prior : ∀ n, n < 425984 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 434176 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h426496 := Path.chunk_sound context_valid decode facts instructions 425984 512
    prior checked_425984
  have h427008 := Path.chunk_sound context_valid decode facts instructions 426496 512
    h426496 checked_426496
  have h427520 := Path.chunk_sound context_valid decode facts instructions 427008 512
    h427008 checked_427008
  have h428032 := Path.chunk_sound context_valid decode facts instructions 427520 512
    h427520 checked_427520
  have h428544 := Path.chunk_sound context_valid decode facts instructions 428032 512
    h428032 checked_428032
  have h429056 := Path.chunk_sound context_valid decode facts instructions 428544 512
    h428544 checked_428544
  have h429568 := Path.chunk_sound context_valid decode facts instructions 429056 512
    h429056 checked_429056
  have h430080 := Path.chunk_sound context_valid decode facts instructions 429568 512
    h429568 checked_429568
  have h430592 := Path.chunk_sound context_valid decode facts instructions 430080 512
    h430080 checked_430080
  have h431104 := Path.chunk_sound context_valid decode facts instructions 430592 512
    h430592 checked_430592
  have h431616 := Path.chunk_sound context_valid decode facts instructions 431104 512
    h431104 checked_431104
  have h432128 := Path.chunk_sound context_valid decode facts instructions 431616 512
    h431616 checked_431616
  have h432640 := Path.chunk_sound context_valid decode facts instructions 432128 512
    h432128 checked_432128
  have h433152 := Path.chunk_sound context_valid decode facts instructions 432640 512
    h432640 checked_432640
  have h433664 := Path.chunk_sound context_valid decode facts instructions 433152 512
    h433152 checked_433152
  have h434176 := Path.chunk_sound context_valid decode facts instructions 433664 512
    h433664 checked_433664
  exact h434176

end Sporadic.Janko3.AmalgamPresentation.Cover
