module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_278528 : Path.checkChunk context decode facts instructions 278528 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_279040 : Path.checkChunk context decode facts instructions 279040 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_279552 : Path.checkChunk context decode facts instructions 279552 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_280064 : Path.checkChunk context decode facts instructions 280064 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_280576 : Path.checkChunk context decode facts instructions 280576 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_281088 : Path.checkChunk context decode facts instructions 281088 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_281600 : Path.checkChunk context decode facts instructions 281600 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_282112 : Path.checkChunk context decode facts instructions 282112 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_282624 : Path.checkChunk context decode facts instructions 282624 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_283136 : Path.checkChunk context decode facts instructions 283136 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_283648 : Path.checkChunk context decode facts instructions 283648 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_284160 : Path.checkChunk context decode facts instructions 284160 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_284672 : Path.checkChunk context decode facts instructions 284672 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_285184 : Path.checkChunk context decode facts instructions 285184 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_285696 : Path.checkChunk context decode facts instructions 285696 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_286208 : Path.checkChunk context decode facts instructions 286208 512 = true := by
  decide +kernel

theorem sound_278528 (prior : ∀ n, n < 278528 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 286720 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h279040 := Path.chunk_sound context_valid decode facts instructions 278528 512
    prior checked_278528
  have h279552 := Path.chunk_sound context_valid decode facts instructions 279040 512
    h279040 checked_279040
  have h280064 := Path.chunk_sound context_valid decode facts instructions 279552 512
    h279552 checked_279552
  have h280576 := Path.chunk_sound context_valid decode facts instructions 280064 512
    h280064 checked_280064
  have h281088 := Path.chunk_sound context_valid decode facts instructions 280576 512
    h280576 checked_280576
  have h281600 := Path.chunk_sound context_valid decode facts instructions 281088 512
    h281088 checked_281088
  have h282112 := Path.chunk_sound context_valid decode facts instructions 281600 512
    h281600 checked_281600
  have h282624 := Path.chunk_sound context_valid decode facts instructions 282112 512
    h282112 checked_282112
  have h283136 := Path.chunk_sound context_valid decode facts instructions 282624 512
    h282624 checked_282624
  have h283648 := Path.chunk_sound context_valid decode facts instructions 283136 512
    h283136 checked_283136
  have h284160 := Path.chunk_sound context_valid decode facts instructions 283648 512
    h283648 checked_283648
  have h284672 := Path.chunk_sound context_valid decode facts instructions 284160 512
    h284160 checked_284160
  have h285184 := Path.chunk_sound context_valid decode facts instructions 284672 512
    h284672 checked_284672
  have h285696 := Path.chunk_sound context_valid decode facts instructions 285184 512
    h285184 checked_285184
  have h286208 := Path.chunk_sound context_valid decode facts instructions 285696 512
    h285696 checked_285696
  have h286720 := Path.chunk_sound context_valid decode facts instructions 286208 512
    h286208 checked_286208
  exact h286720

end Sporadic.Janko3.AmalgamPresentation.Cover
