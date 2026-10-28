module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_516096 : Path.checkChunk context decode facts instructions 516096 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_516608 : Path.checkChunk context decode facts instructions 516608 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_517120 : Path.checkChunk context decode facts instructions 517120 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_517632 : Path.checkChunk context decode facts instructions 517632 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_518144 : Path.checkChunk context decode facts instructions 518144 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_518656 : Path.checkChunk context decode facts instructions 518656 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_519168 : Path.checkChunk context decode facts instructions 519168 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_519680 : Path.checkChunk context decode facts instructions 519680 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_520192 : Path.checkChunk context decode facts instructions 520192 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_520704 : Path.checkChunk context decode facts instructions 520704 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_521216 : Path.checkChunk context decode facts instructions 521216 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_521728 : Path.checkChunk context decode facts instructions 521728 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_522240 : Path.checkChunk context decode facts instructions 522240 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_522752 : Path.checkChunk context decode facts instructions 522752 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_523264 : Path.checkChunk context decode facts instructions 523264 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_523776 : Path.checkChunk context decode facts instructions 523776 512 = true := by
  decide +kernel

theorem sound_516096 (prior : ∀ n, n < 516096 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 524288 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h516608 := Path.chunk_sound context_valid decode facts instructions 516096 512
    prior checked_516096
  have h517120 := Path.chunk_sound context_valid decode facts instructions 516608 512
    h516608 checked_516608
  have h517632 := Path.chunk_sound context_valid decode facts instructions 517120 512
    h517120 checked_517120
  have h518144 := Path.chunk_sound context_valid decode facts instructions 517632 512
    h517632 checked_517632
  have h518656 := Path.chunk_sound context_valid decode facts instructions 518144 512
    h518144 checked_518144
  have h519168 := Path.chunk_sound context_valid decode facts instructions 518656 512
    h518656 checked_518656
  have h519680 := Path.chunk_sound context_valid decode facts instructions 519168 512
    h519168 checked_519168
  have h520192 := Path.chunk_sound context_valid decode facts instructions 519680 512
    h519680 checked_519680
  have h520704 := Path.chunk_sound context_valid decode facts instructions 520192 512
    h520192 checked_520192
  have h521216 := Path.chunk_sound context_valid decode facts instructions 520704 512
    h520704 checked_520704
  have h521728 := Path.chunk_sound context_valid decode facts instructions 521216 512
    h521216 checked_521216
  have h522240 := Path.chunk_sound context_valid decode facts instructions 521728 512
    h521728 checked_521728
  have h522752 := Path.chunk_sound context_valid decode facts instructions 522240 512
    h522240 checked_522240
  have h523264 := Path.chunk_sound context_valid decode facts instructions 522752 512
    h522752 checked_522752
  have h523776 := Path.chunk_sound context_valid decode facts instructions 523264 512
    h523264 checked_523264
  have h524288 := Path.chunk_sound context_valid decode facts instructions 523776 512
    h523776 checked_523776
  exact h524288

end Sporadic.Janko3.AmalgamPresentation.Cover
