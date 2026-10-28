module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_851968 : Path.checkChunk context decode facts instructions 851968 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_852480 : Path.checkChunk context decode facts instructions 852480 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_852992 : Path.checkChunk context decode facts instructions 852992 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_853504 : Path.checkChunk context decode facts instructions 853504 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_854016 : Path.checkChunk context decode facts instructions 854016 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_854528 : Path.checkChunk context decode facts instructions 854528 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_855040 : Path.checkChunk context decode facts instructions 855040 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_855552 : Path.checkChunk context decode facts instructions 855552 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_856064 : Path.checkChunk context decode facts instructions 856064 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_856576 : Path.checkChunk context decode facts instructions 856576 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_857088 : Path.checkChunk context decode facts instructions 857088 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_857600 : Path.checkChunk context decode facts instructions 857600 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_858112 : Path.checkChunk context decode facts instructions 858112 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_858624 : Path.checkChunk context decode facts instructions 858624 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_859136 : Path.checkChunk context decode facts instructions 859136 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_859648 : Path.checkChunk context decode facts instructions 859648 512 = true := by
  decide +kernel

theorem sound_851968 (prior : ∀ n, n < 851968 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 860160 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h852480 := Path.chunk_sound context_valid decode facts instructions 851968 512
    prior checked_851968
  have h852992 := Path.chunk_sound context_valid decode facts instructions 852480 512
    h852480 checked_852480
  have h853504 := Path.chunk_sound context_valid decode facts instructions 852992 512
    h852992 checked_852992
  have h854016 := Path.chunk_sound context_valid decode facts instructions 853504 512
    h853504 checked_853504
  have h854528 := Path.chunk_sound context_valid decode facts instructions 854016 512
    h854016 checked_854016
  have h855040 := Path.chunk_sound context_valid decode facts instructions 854528 512
    h854528 checked_854528
  have h855552 := Path.chunk_sound context_valid decode facts instructions 855040 512
    h855040 checked_855040
  have h856064 := Path.chunk_sound context_valid decode facts instructions 855552 512
    h855552 checked_855552
  have h856576 := Path.chunk_sound context_valid decode facts instructions 856064 512
    h856064 checked_856064
  have h857088 := Path.chunk_sound context_valid decode facts instructions 856576 512
    h856576 checked_856576
  have h857600 := Path.chunk_sound context_valid decode facts instructions 857088 512
    h857088 checked_857088
  have h858112 := Path.chunk_sound context_valid decode facts instructions 857600 512
    h857600 checked_857600
  have h858624 := Path.chunk_sound context_valid decode facts instructions 858112 512
    h858112 checked_858112
  have h859136 := Path.chunk_sound context_valid decode facts instructions 858624 512
    h858624 checked_858624
  have h859648 := Path.chunk_sound context_valid decode facts instructions 859136 512
    h859136 checked_859136
  have h860160 := Path.chunk_sound context_valid decode facts instructions 859648 512
    h859648 checked_859648
  exact h860160

end Sporadic.Janko3.AmalgamPresentation.Cover
