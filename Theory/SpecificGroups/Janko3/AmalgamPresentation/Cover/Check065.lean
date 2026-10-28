module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_532480 : Path.checkChunk context decode facts instructions 532480 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_532992 : Path.checkChunk context decode facts instructions 532992 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_533504 : Path.checkChunk context decode facts instructions 533504 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_534016 : Path.checkChunk context decode facts instructions 534016 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_534528 : Path.checkChunk context decode facts instructions 534528 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_535040 : Path.checkChunk context decode facts instructions 535040 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_535552 : Path.checkChunk context decode facts instructions 535552 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_536064 : Path.checkChunk context decode facts instructions 536064 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_536576 : Path.checkChunk context decode facts instructions 536576 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_537088 : Path.checkChunk context decode facts instructions 537088 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_537600 : Path.checkChunk context decode facts instructions 537600 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_538112 : Path.checkChunk context decode facts instructions 538112 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_538624 : Path.checkChunk context decode facts instructions 538624 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_539136 : Path.checkChunk context decode facts instructions 539136 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_539648 : Path.checkChunk context decode facts instructions 539648 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_540160 : Path.checkChunk context decode facts instructions 540160 512 = true := by
  decide +kernel

theorem sound_532480 (prior : ∀ n, n < 532480 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 540672 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h532992 := Path.chunk_sound context_valid decode facts instructions 532480 512
    prior checked_532480
  have h533504 := Path.chunk_sound context_valid decode facts instructions 532992 512
    h532992 checked_532992
  have h534016 := Path.chunk_sound context_valid decode facts instructions 533504 512
    h533504 checked_533504
  have h534528 := Path.chunk_sound context_valid decode facts instructions 534016 512
    h534016 checked_534016
  have h535040 := Path.chunk_sound context_valid decode facts instructions 534528 512
    h534528 checked_534528
  have h535552 := Path.chunk_sound context_valid decode facts instructions 535040 512
    h535040 checked_535040
  have h536064 := Path.chunk_sound context_valid decode facts instructions 535552 512
    h535552 checked_535552
  have h536576 := Path.chunk_sound context_valid decode facts instructions 536064 512
    h536064 checked_536064
  have h537088 := Path.chunk_sound context_valid decode facts instructions 536576 512
    h536576 checked_536576
  have h537600 := Path.chunk_sound context_valid decode facts instructions 537088 512
    h537088 checked_537088
  have h538112 := Path.chunk_sound context_valid decode facts instructions 537600 512
    h537600 checked_537600
  have h538624 := Path.chunk_sound context_valid decode facts instructions 538112 512
    h538112 checked_538112
  have h539136 := Path.chunk_sound context_valid decode facts instructions 538624 512
    h538624 checked_538624
  have h539648 := Path.chunk_sound context_valid decode facts instructions 539136 512
    h539136 checked_539136
  have h540160 := Path.chunk_sound context_valid decode facts instructions 539648 512
    h539648 checked_539648
  have h540672 := Path.chunk_sound context_valid decode facts instructions 540160 512
    h540160 checked_540160
  exact h540672

end Sporadic.Janko3.AmalgamPresentation.Cover
