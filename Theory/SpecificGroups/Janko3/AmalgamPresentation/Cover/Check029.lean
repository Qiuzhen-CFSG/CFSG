module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_237568 : Path.checkChunk context decode facts instructions 237568 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_238080 : Path.checkChunk context decode facts instructions 238080 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_238592 : Path.checkChunk context decode facts instructions 238592 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_239104 : Path.checkChunk context decode facts instructions 239104 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_239616 : Path.checkChunk context decode facts instructions 239616 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_240128 : Path.checkChunk context decode facts instructions 240128 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_240640 : Path.checkChunk context decode facts instructions 240640 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_241152 : Path.checkChunk context decode facts instructions 241152 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_241664 : Path.checkChunk context decode facts instructions 241664 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_242176 : Path.checkChunk context decode facts instructions 242176 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_242688 : Path.checkChunk context decode facts instructions 242688 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_243200 : Path.checkChunk context decode facts instructions 243200 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_243712 : Path.checkChunk context decode facts instructions 243712 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_244224 : Path.checkChunk context decode facts instructions 244224 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_244736 : Path.checkChunk context decode facts instructions 244736 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_245248 : Path.checkChunk context decode facts instructions 245248 512 = true := by
  decide +kernel

theorem sound_237568 (prior : ∀ n, n < 237568 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 245760 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h238080 := Path.chunk_sound context_valid decode facts instructions 237568 512
    prior checked_237568
  have h238592 := Path.chunk_sound context_valid decode facts instructions 238080 512
    h238080 checked_238080
  have h239104 := Path.chunk_sound context_valid decode facts instructions 238592 512
    h238592 checked_238592
  have h239616 := Path.chunk_sound context_valid decode facts instructions 239104 512
    h239104 checked_239104
  have h240128 := Path.chunk_sound context_valid decode facts instructions 239616 512
    h239616 checked_239616
  have h240640 := Path.chunk_sound context_valid decode facts instructions 240128 512
    h240128 checked_240128
  have h241152 := Path.chunk_sound context_valid decode facts instructions 240640 512
    h240640 checked_240640
  have h241664 := Path.chunk_sound context_valid decode facts instructions 241152 512
    h241152 checked_241152
  have h242176 := Path.chunk_sound context_valid decode facts instructions 241664 512
    h241664 checked_241664
  have h242688 := Path.chunk_sound context_valid decode facts instructions 242176 512
    h242176 checked_242176
  have h243200 := Path.chunk_sound context_valid decode facts instructions 242688 512
    h242688 checked_242688
  have h243712 := Path.chunk_sound context_valid decode facts instructions 243200 512
    h243200 checked_243200
  have h244224 := Path.chunk_sound context_valid decode facts instructions 243712 512
    h243712 checked_243712
  have h244736 := Path.chunk_sound context_valid decode facts instructions 244224 512
    h244224 checked_244224
  have h245248 := Path.chunk_sound context_valid decode facts instructions 244736 512
    h244736 checked_244736
  have h245760 := Path.chunk_sound context_valid decode facts instructions 245248 512
    h245248 checked_245248
  exact h245760

end Sporadic.Janko3.AmalgamPresentation.Cover
