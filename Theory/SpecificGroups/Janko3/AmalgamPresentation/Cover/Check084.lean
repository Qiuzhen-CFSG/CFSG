module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_688128 : Path.checkChunk context decode facts instructions 688128 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_688640 : Path.checkChunk context decode facts instructions 688640 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_689152 : Path.checkChunk context decode facts instructions 689152 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_689664 : Path.checkChunk context decode facts instructions 689664 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_690176 : Path.checkChunk context decode facts instructions 690176 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_690688 : Path.checkChunk context decode facts instructions 690688 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_691200 : Path.checkChunk context decode facts instructions 691200 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_691712 : Path.checkChunk context decode facts instructions 691712 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_692224 : Path.checkChunk context decode facts instructions 692224 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_692736 : Path.checkChunk context decode facts instructions 692736 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_693248 : Path.checkChunk context decode facts instructions 693248 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_693760 : Path.checkChunk context decode facts instructions 693760 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_694272 : Path.checkChunk context decode facts instructions 694272 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_694784 : Path.checkChunk context decode facts instructions 694784 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_695296 : Path.checkChunk context decode facts instructions 695296 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_695808 : Path.checkChunk context decode facts instructions 695808 512 = true := by
  decide +kernel

theorem sound_688128 (prior : ∀ n, n < 688128 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 696320 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h688640 := Path.chunk_sound context_valid decode facts instructions 688128 512
    prior checked_688128
  have h689152 := Path.chunk_sound context_valid decode facts instructions 688640 512
    h688640 checked_688640
  have h689664 := Path.chunk_sound context_valid decode facts instructions 689152 512
    h689152 checked_689152
  have h690176 := Path.chunk_sound context_valid decode facts instructions 689664 512
    h689664 checked_689664
  have h690688 := Path.chunk_sound context_valid decode facts instructions 690176 512
    h690176 checked_690176
  have h691200 := Path.chunk_sound context_valid decode facts instructions 690688 512
    h690688 checked_690688
  have h691712 := Path.chunk_sound context_valid decode facts instructions 691200 512
    h691200 checked_691200
  have h692224 := Path.chunk_sound context_valid decode facts instructions 691712 512
    h691712 checked_691712
  have h692736 := Path.chunk_sound context_valid decode facts instructions 692224 512
    h692224 checked_692224
  have h693248 := Path.chunk_sound context_valid decode facts instructions 692736 512
    h692736 checked_692736
  have h693760 := Path.chunk_sound context_valid decode facts instructions 693248 512
    h693248 checked_693248
  have h694272 := Path.chunk_sound context_valid decode facts instructions 693760 512
    h693760 checked_693760
  have h694784 := Path.chunk_sound context_valid decode facts instructions 694272 512
    h694272 checked_694272
  have h695296 := Path.chunk_sound context_valid decode facts instructions 694784 512
    h694784 checked_694784
  have h695808 := Path.chunk_sound context_valid decode facts instructions 695296 512
    h695296 checked_695296
  have h696320 := Path.chunk_sound context_valid decode facts instructions 695808 512
    h695808 checked_695808
  exact h696320

end Sporadic.Janko3.AmalgamPresentation.Cover
