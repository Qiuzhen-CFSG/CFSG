module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_811008 : Path.checkChunk context decode facts instructions 811008 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_811520 : Path.checkChunk context decode facts instructions 811520 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_812032 : Path.checkChunk context decode facts instructions 812032 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_812544 : Path.checkChunk context decode facts instructions 812544 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_813056 : Path.checkChunk context decode facts instructions 813056 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_813568 : Path.checkChunk context decode facts instructions 813568 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_814080 : Path.checkChunk context decode facts instructions 814080 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_814592 : Path.checkChunk context decode facts instructions 814592 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_815104 : Path.checkChunk context decode facts instructions 815104 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_815616 : Path.checkChunk context decode facts instructions 815616 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_816128 : Path.checkChunk context decode facts instructions 816128 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_816640 : Path.checkChunk context decode facts instructions 816640 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_817152 : Path.checkChunk context decode facts instructions 817152 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_817664 : Path.checkChunk context decode facts instructions 817664 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_818176 : Path.checkChunk context decode facts instructions 818176 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_818688 : Path.checkChunk context decode facts instructions 818688 512 = true := by
  decide +kernel

theorem sound_811008 (prior : ∀ n, n < 811008 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 819200 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h811520 := Path.chunk_sound context_valid decode facts instructions 811008 512
    prior checked_811008
  have h812032 := Path.chunk_sound context_valid decode facts instructions 811520 512
    h811520 checked_811520
  have h812544 := Path.chunk_sound context_valid decode facts instructions 812032 512
    h812032 checked_812032
  have h813056 := Path.chunk_sound context_valid decode facts instructions 812544 512
    h812544 checked_812544
  have h813568 := Path.chunk_sound context_valid decode facts instructions 813056 512
    h813056 checked_813056
  have h814080 := Path.chunk_sound context_valid decode facts instructions 813568 512
    h813568 checked_813568
  have h814592 := Path.chunk_sound context_valid decode facts instructions 814080 512
    h814080 checked_814080
  have h815104 := Path.chunk_sound context_valid decode facts instructions 814592 512
    h814592 checked_814592
  have h815616 := Path.chunk_sound context_valid decode facts instructions 815104 512
    h815104 checked_815104
  have h816128 := Path.chunk_sound context_valid decode facts instructions 815616 512
    h815616 checked_815616
  have h816640 := Path.chunk_sound context_valid decode facts instructions 816128 512
    h816128 checked_816128
  have h817152 := Path.chunk_sound context_valid decode facts instructions 816640 512
    h816640 checked_816640
  have h817664 := Path.chunk_sound context_valid decode facts instructions 817152 512
    h817152 checked_817152
  have h818176 := Path.chunk_sound context_valid decode facts instructions 817664 512
    h817664 checked_817664
  have h818688 := Path.chunk_sound context_valid decode facts instructions 818176 512
    h818176 checked_818176
  have h819200 := Path.chunk_sound context_valid decode facts instructions 818688 512
    h818688 checked_818688
  exact h819200

end Sporadic.Janko3.AmalgamPresentation.Cover
