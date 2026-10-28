module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_753664 : Path.checkChunk context decode facts instructions 753664 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_754176 : Path.checkChunk context decode facts instructions 754176 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_754688 : Path.checkChunk context decode facts instructions 754688 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_755200 : Path.checkChunk context decode facts instructions 755200 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_755712 : Path.checkChunk context decode facts instructions 755712 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_756224 : Path.checkChunk context decode facts instructions 756224 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_756736 : Path.checkChunk context decode facts instructions 756736 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_757248 : Path.checkChunk context decode facts instructions 757248 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_757760 : Path.checkChunk context decode facts instructions 757760 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_758272 : Path.checkChunk context decode facts instructions 758272 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_758784 : Path.checkChunk context decode facts instructions 758784 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_759296 : Path.checkChunk context decode facts instructions 759296 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_759808 : Path.checkChunk context decode facts instructions 759808 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_760320 : Path.checkChunk context decode facts instructions 760320 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_760832 : Path.checkChunk context decode facts instructions 760832 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_761344 : Path.checkChunk context decode facts instructions 761344 512 = true := by
  decide +kernel

theorem sound_753664 (prior : ∀ n, n < 753664 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 761856 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h754176 := Path.chunk_sound context_valid decode facts instructions 753664 512
    prior checked_753664
  have h754688 := Path.chunk_sound context_valid decode facts instructions 754176 512
    h754176 checked_754176
  have h755200 := Path.chunk_sound context_valid decode facts instructions 754688 512
    h754688 checked_754688
  have h755712 := Path.chunk_sound context_valid decode facts instructions 755200 512
    h755200 checked_755200
  have h756224 := Path.chunk_sound context_valid decode facts instructions 755712 512
    h755712 checked_755712
  have h756736 := Path.chunk_sound context_valid decode facts instructions 756224 512
    h756224 checked_756224
  have h757248 := Path.chunk_sound context_valid decode facts instructions 756736 512
    h756736 checked_756736
  have h757760 := Path.chunk_sound context_valid decode facts instructions 757248 512
    h757248 checked_757248
  have h758272 := Path.chunk_sound context_valid decode facts instructions 757760 512
    h757760 checked_757760
  have h758784 := Path.chunk_sound context_valid decode facts instructions 758272 512
    h758272 checked_758272
  have h759296 := Path.chunk_sound context_valid decode facts instructions 758784 512
    h758784 checked_758784
  have h759808 := Path.chunk_sound context_valid decode facts instructions 759296 512
    h759296 checked_759296
  have h760320 := Path.chunk_sound context_valid decode facts instructions 759808 512
    h759808 checked_759808
  have h760832 := Path.chunk_sound context_valid decode facts instructions 760320 512
    h760320 checked_760320
  have h761344 := Path.chunk_sound context_valid decode facts instructions 760832 512
    h760832 checked_760832
  have h761856 := Path.chunk_sound context_valid decode facts instructions 761344 512
    h761344 checked_761344
  exact h761856

end Sporadic.Janko3.AmalgamPresentation.Cover
