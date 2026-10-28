module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.Tables

/-! Centralizer-coset certificate for the thirteen ATLAS HS relators.
Untrusted data generated from the retained trace; all deduction checks use
Lean's kernel and the actual abstract relations. See `source/README.md`. -/

public section
namespace Sporadic.LeechRelated.HS.AtlasPresentation.Exact.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 4096 in
theorem checked_229376 : Scan.checkChunk context facts instructions 229376 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_229888 : Scan.checkChunk context facts instructions 229888 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_230400 : Scan.checkChunk context facts instructions 230400 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_230912 : Scan.checkChunk context facts instructions 230912 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_231424 : Scan.checkChunk context facts instructions 231424 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_231936 : Scan.checkChunk context facts instructions 231936 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_232448 : Scan.checkChunk context facts instructions 232448 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_232960 : Scan.checkChunk context facts instructions 232960 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_233472 : Scan.checkChunk context facts instructions 233472 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_233984 : Scan.checkChunk context facts instructions 233984 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_234496 : Scan.checkChunk context facts instructions 234496 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_235008 : Scan.checkChunk context facts instructions 235008 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_235520 : Scan.checkChunk context facts instructions 235520 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_236032 : Scan.checkChunk context facts instructions 236032 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_236544 : Scan.checkChunk context facts instructions 236544 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_237056 : Scan.checkChunk context facts instructions 237056 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_237568 : Scan.checkChunk context facts instructions 237568 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_238080 : Scan.checkChunk context facts instructions 238080 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_238592 : Scan.checkChunk context facts instructions 238592 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_239104 : Scan.checkChunk context facts instructions 239104 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_239616 : Scan.checkChunk context facts instructions 239616 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_240128 : Scan.checkChunk context facts instructions 240128 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_240640 : Scan.checkChunk context facts instructions 240640 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_241152 : Scan.checkChunk context facts instructions 241152 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_241664 : Scan.checkChunk context facts instructions 241664 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_242176 : Scan.checkChunk context facts instructions 242176 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_242688 : Scan.checkChunk context facts instructions 242688 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_243200 : Scan.checkChunk context facts instructions 243200 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_243712 : Scan.checkChunk context facts instructions 243712 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_244224 : Scan.checkChunk context facts instructions 244224 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_244736 : Scan.checkChunk context facts instructions 244736 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_245248 : Scan.checkChunk context facts instructions 245248 512 = true := by
  decide +kernel

theorem all_hold_245760 (prior : ∀ n, n < 229376 → Holds centralizer certGenerator (definitions.repr certGenerator) (facts n)) : ∀ n, n < 245760 →
    Holds centralizer certGenerator (definitions.repr certGenerator) (facts n) := by
  have h229888 := Scan.chunk_sound context_valid facts instructions 229376 512
    prior checked_229376
  have h230400 := Scan.chunk_sound context_valid facts instructions 229888 512
    h229888 checked_229888
  have h230912 := Scan.chunk_sound context_valid facts instructions 230400 512
    h230400 checked_230400
  have h231424 := Scan.chunk_sound context_valid facts instructions 230912 512
    h230912 checked_230912
  have h231936 := Scan.chunk_sound context_valid facts instructions 231424 512
    h231424 checked_231424
  have h232448 := Scan.chunk_sound context_valid facts instructions 231936 512
    h231936 checked_231936
  have h232960 := Scan.chunk_sound context_valid facts instructions 232448 512
    h232448 checked_232448
  have h233472 := Scan.chunk_sound context_valid facts instructions 232960 512
    h232960 checked_232960
  have h233984 := Scan.chunk_sound context_valid facts instructions 233472 512
    h233472 checked_233472
  have h234496 := Scan.chunk_sound context_valid facts instructions 233984 512
    h233984 checked_233984
  have h235008 := Scan.chunk_sound context_valid facts instructions 234496 512
    h234496 checked_234496
  have h235520 := Scan.chunk_sound context_valid facts instructions 235008 512
    h235008 checked_235008
  have h236032 := Scan.chunk_sound context_valid facts instructions 235520 512
    h235520 checked_235520
  have h236544 := Scan.chunk_sound context_valid facts instructions 236032 512
    h236032 checked_236032
  have h237056 := Scan.chunk_sound context_valid facts instructions 236544 512
    h236544 checked_236544
  have h237568 := Scan.chunk_sound context_valid facts instructions 237056 512
    h237056 checked_237056
  have h238080 := Scan.chunk_sound context_valid facts instructions 237568 512
    h237568 checked_237568
  have h238592 := Scan.chunk_sound context_valid facts instructions 238080 512
    h238080 checked_238080
  have h239104 := Scan.chunk_sound context_valid facts instructions 238592 512
    h238592 checked_238592
  have h239616 := Scan.chunk_sound context_valid facts instructions 239104 512
    h239104 checked_239104
  have h240128 := Scan.chunk_sound context_valid facts instructions 239616 512
    h239616 checked_239616
  have h240640 := Scan.chunk_sound context_valid facts instructions 240128 512
    h240128 checked_240128
  have h241152 := Scan.chunk_sound context_valid facts instructions 240640 512
    h240640 checked_240640
  have h241664 := Scan.chunk_sound context_valid facts instructions 241152 512
    h241152 checked_241152
  have h242176 := Scan.chunk_sound context_valid facts instructions 241664 512
    h241664 checked_241664
  have h242688 := Scan.chunk_sound context_valid facts instructions 242176 512
    h242176 checked_242176
  have h243200 := Scan.chunk_sound context_valid facts instructions 242688 512
    h242688 checked_242688
  have h243712 := Scan.chunk_sound context_valid facts instructions 243200 512
    h243200 checked_243200
  have h244224 := Scan.chunk_sound context_valid facts instructions 243712 512
    h243712 checked_243712
  have h244736 := Scan.chunk_sound context_valid facts instructions 244224 512
    h244224 checked_244224
  have h245248 := Scan.chunk_sound context_valid facts instructions 244736 512
    h244736 checked_244736
  have h245760 := Scan.chunk_sound context_valid facts instructions 245248 512
    h245248 checked_245248
  exact h245760

end Sporadic.LeechRelated.HS.AtlasPresentation.Exact.Cover
