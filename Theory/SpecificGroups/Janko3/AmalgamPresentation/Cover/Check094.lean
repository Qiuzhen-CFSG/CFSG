module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_770048 : Path.checkChunk context decode facts instructions 770048 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_770560 : Path.checkChunk context decode facts instructions 770560 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_771072 : Path.checkChunk context decode facts instructions 771072 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_771584 : Path.checkChunk context decode facts instructions 771584 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_772096 : Path.checkChunk context decode facts instructions 772096 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_772608 : Path.checkChunk context decode facts instructions 772608 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_773120 : Path.checkChunk context decode facts instructions 773120 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_773632 : Path.checkChunk context decode facts instructions 773632 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_774144 : Path.checkChunk context decode facts instructions 774144 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_774656 : Path.checkChunk context decode facts instructions 774656 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_775168 : Path.checkChunk context decode facts instructions 775168 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_775680 : Path.checkChunk context decode facts instructions 775680 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_776192 : Path.checkChunk context decode facts instructions 776192 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_776704 : Path.checkChunk context decode facts instructions 776704 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_777216 : Path.checkChunk context decode facts instructions 777216 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_777728 : Path.checkChunk context decode facts instructions 777728 512 = true := by
  decide +kernel

theorem sound_770048 (prior : ∀ n, n < 770048 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 778240 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h770560 := Path.chunk_sound context_valid decode facts instructions 770048 512
    prior checked_770048
  have h771072 := Path.chunk_sound context_valid decode facts instructions 770560 512
    h770560 checked_770560
  have h771584 := Path.chunk_sound context_valid decode facts instructions 771072 512
    h771072 checked_771072
  have h772096 := Path.chunk_sound context_valid decode facts instructions 771584 512
    h771584 checked_771584
  have h772608 := Path.chunk_sound context_valid decode facts instructions 772096 512
    h772096 checked_772096
  have h773120 := Path.chunk_sound context_valid decode facts instructions 772608 512
    h772608 checked_772608
  have h773632 := Path.chunk_sound context_valid decode facts instructions 773120 512
    h773120 checked_773120
  have h774144 := Path.chunk_sound context_valid decode facts instructions 773632 512
    h773632 checked_773632
  have h774656 := Path.chunk_sound context_valid decode facts instructions 774144 512
    h774144 checked_774144
  have h775168 := Path.chunk_sound context_valid decode facts instructions 774656 512
    h774656 checked_774656
  have h775680 := Path.chunk_sound context_valid decode facts instructions 775168 512
    h775168 checked_775168
  have h776192 := Path.chunk_sound context_valid decode facts instructions 775680 512
    h775680 checked_775680
  have h776704 := Path.chunk_sound context_valid decode facts instructions 776192 512
    h776192 checked_776192
  have h777216 := Path.chunk_sound context_valid decode facts instructions 776704 512
    h776704 checked_776704
  have h777728 := Path.chunk_sound context_valid decode facts instructions 777216 512
    h777216 checked_777216
  have h778240 := Path.chunk_sound context_valid decode facts instructions 777728 512
    h777728 checked_777728
  exact h778240

end Sporadic.Janko3.AmalgamPresentation.Cover
