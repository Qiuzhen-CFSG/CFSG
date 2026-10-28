module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_942080 : Path.checkChunk context decode facts instructions 942080 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_942592 : Path.checkChunk context decode facts instructions 942592 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_943104 : Path.checkChunk context decode facts instructions 943104 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_943616 : Path.checkChunk context decode facts instructions 943616 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_944128 : Path.checkChunk context decode facts instructions 944128 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_944640 : Path.checkChunk context decode facts instructions 944640 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_945152 : Path.checkChunk context decode facts instructions 945152 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_945664 : Path.checkChunk context decode facts instructions 945664 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_946176 : Path.checkChunk context decode facts instructions 946176 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_946688 : Path.checkChunk context decode facts instructions 946688 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_947200 : Path.checkChunk context decode facts instructions 947200 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_947712 : Path.checkChunk context decode facts instructions 947712 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_948224 : Path.checkChunk context decode facts instructions 948224 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_948736 : Path.checkChunk context decode facts instructions 948736 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_949248 : Path.checkChunk context decode facts instructions 949248 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_949760 : Path.checkChunk context decode facts instructions 949760 512 = true := by
  decide +kernel

theorem sound_942080 (prior : ∀ n, n < 942080 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 950272 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h942592 := Path.chunk_sound context_valid decode facts instructions 942080 512
    prior checked_942080
  have h943104 := Path.chunk_sound context_valid decode facts instructions 942592 512
    h942592 checked_942592
  have h943616 := Path.chunk_sound context_valid decode facts instructions 943104 512
    h943104 checked_943104
  have h944128 := Path.chunk_sound context_valid decode facts instructions 943616 512
    h943616 checked_943616
  have h944640 := Path.chunk_sound context_valid decode facts instructions 944128 512
    h944128 checked_944128
  have h945152 := Path.chunk_sound context_valid decode facts instructions 944640 512
    h944640 checked_944640
  have h945664 := Path.chunk_sound context_valid decode facts instructions 945152 512
    h945152 checked_945152
  have h946176 := Path.chunk_sound context_valid decode facts instructions 945664 512
    h945664 checked_945664
  have h946688 := Path.chunk_sound context_valid decode facts instructions 946176 512
    h946176 checked_946176
  have h947200 := Path.chunk_sound context_valid decode facts instructions 946688 512
    h946688 checked_946688
  have h947712 := Path.chunk_sound context_valid decode facts instructions 947200 512
    h947200 checked_947200
  have h948224 := Path.chunk_sound context_valid decode facts instructions 947712 512
    h947712 checked_947712
  have h948736 := Path.chunk_sound context_valid decode facts instructions 948224 512
    h948224 checked_948224
  have h949248 := Path.chunk_sound context_valid decode facts instructions 948736 512
    h948736 checked_948736
  have h949760 := Path.chunk_sound context_valid decode facts instructions 949248 512
    h949248 checked_949248
  have h950272 := Path.chunk_sound context_valid decode facts instructions 949760 512
    h949760 checked_949760
  exact h950272

end Sporadic.Janko3.AmalgamPresentation.Cover
