module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_598016 : Path.checkChunk context decode facts instructions 598016 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_598528 : Path.checkChunk context decode facts instructions 598528 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_599040 : Path.checkChunk context decode facts instructions 599040 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_599552 : Path.checkChunk context decode facts instructions 599552 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_600064 : Path.checkChunk context decode facts instructions 600064 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_600576 : Path.checkChunk context decode facts instructions 600576 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_601088 : Path.checkChunk context decode facts instructions 601088 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_601600 : Path.checkChunk context decode facts instructions 601600 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_602112 : Path.checkChunk context decode facts instructions 602112 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_602624 : Path.checkChunk context decode facts instructions 602624 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_603136 : Path.checkChunk context decode facts instructions 603136 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_603648 : Path.checkChunk context decode facts instructions 603648 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_604160 : Path.checkChunk context decode facts instructions 604160 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_604672 : Path.checkChunk context decode facts instructions 604672 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_605184 : Path.checkChunk context decode facts instructions 605184 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_605696 : Path.checkChunk context decode facts instructions 605696 512 = true := by
  decide +kernel

theorem sound_598016 (prior : ∀ n, n < 598016 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 606208 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h598528 := Path.chunk_sound context_valid decode facts instructions 598016 512
    prior checked_598016
  have h599040 := Path.chunk_sound context_valid decode facts instructions 598528 512
    h598528 checked_598528
  have h599552 := Path.chunk_sound context_valid decode facts instructions 599040 512
    h599040 checked_599040
  have h600064 := Path.chunk_sound context_valid decode facts instructions 599552 512
    h599552 checked_599552
  have h600576 := Path.chunk_sound context_valid decode facts instructions 600064 512
    h600064 checked_600064
  have h601088 := Path.chunk_sound context_valid decode facts instructions 600576 512
    h600576 checked_600576
  have h601600 := Path.chunk_sound context_valid decode facts instructions 601088 512
    h601088 checked_601088
  have h602112 := Path.chunk_sound context_valid decode facts instructions 601600 512
    h601600 checked_601600
  have h602624 := Path.chunk_sound context_valid decode facts instructions 602112 512
    h602112 checked_602112
  have h603136 := Path.chunk_sound context_valid decode facts instructions 602624 512
    h602624 checked_602624
  have h603648 := Path.chunk_sound context_valid decode facts instructions 603136 512
    h603136 checked_603136
  have h604160 := Path.chunk_sound context_valid decode facts instructions 603648 512
    h603648 checked_603648
  have h604672 := Path.chunk_sound context_valid decode facts instructions 604160 512
    h604160 checked_604160
  have h605184 := Path.chunk_sound context_valid decode facts instructions 604672 512
    h604672 checked_604672
  have h605696 := Path.chunk_sound context_valid decode facts instructions 605184 512
    h605184 checked_605184
  have h606208 := Path.chunk_sound context_valid decode facts instructions 605696 512
    h605696 checked_605696
  exact h606208

end Sporadic.Janko3.AmalgamPresentation.Cover
