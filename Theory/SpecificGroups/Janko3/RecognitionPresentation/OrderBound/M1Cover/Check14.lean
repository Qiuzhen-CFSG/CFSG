module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Tables

/-! Kernel-checked deductions for the literal ATLAS J3G1-P1 subgroup M₁.
Chunks bound the reduction cache; each scan uses previously proved equations. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 4096 in
theorem checked_229376 : Scan.checkChunk context facts instructions 229376 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_230400 : Scan.checkChunk context facts instructions 230400 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_231424 : Scan.checkChunk context facts instructions 231424 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_232448 : Scan.checkChunk context facts instructions 232448 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_233472 : Scan.checkChunk context facts instructions 233472 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_234496 : Scan.checkChunk context facts instructions 234496 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_235520 : Scan.checkChunk context facts instructions 235520 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_236544 : Scan.checkChunk context facts instructions 236544 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_237568 : Scan.checkChunk context facts instructions 237568 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_238592 : Scan.checkChunk context facts instructions 238592 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_239616 : Scan.checkChunk context facts instructions 239616 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_240640 : Scan.checkChunk context facts instructions 240640 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_241664 : Scan.checkChunk context facts instructions 241664 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_242688 : Scan.checkChunk context facts instructions 242688 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_243712 : Scan.checkChunk context facts instructions 243712 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_244736 : Scan.checkChunk context facts instructions 244736 1024 = true := by
  decide +kernel

theorem sound_229376 (prior : ∀ n, n < 229376 →
    Holds M1 generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 245760 → Holds M1 generator (definitions.repr generator) (facts n) := by
  have h230400 := Scan.chunk_sound context_valid facts instructions 229376 1024
    prior checked_229376
  have h231424 := Scan.chunk_sound context_valid facts instructions 230400 1024
    h230400 checked_230400
  have h232448 := Scan.chunk_sound context_valid facts instructions 231424 1024
    h231424 checked_231424
  have h233472 := Scan.chunk_sound context_valid facts instructions 232448 1024
    h232448 checked_232448
  have h234496 := Scan.chunk_sound context_valid facts instructions 233472 1024
    h233472 checked_233472
  have h235520 := Scan.chunk_sound context_valid facts instructions 234496 1024
    h234496 checked_234496
  have h236544 := Scan.chunk_sound context_valid facts instructions 235520 1024
    h235520 checked_235520
  have h237568 := Scan.chunk_sound context_valid facts instructions 236544 1024
    h236544 checked_236544
  have h238592 := Scan.chunk_sound context_valid facts instructions 237568 1024
    h237568 checked_237568
  have h239616 := Scan.chunk_sound context_valid facts instructions 238592 1024
    h238592 checked_238592
  have h240640 := Scan.chunk_sound context_valid facts instructions 239616 1024
    h239616 checked_239616
  have h241664 := Scan.chunk_sound context_valid facts instructions 240640 1024
    h240640 checked_240640
  have h242688 := Scan.chunk_sound context_valid facts instructions 241664 1024
    h241664 checked_241664
  have h243712 := Scan.chunk_sound context_valid facts instructions 242688 1024
    h242688 checked_242688
  have h244736 := Scan.chunk_sound context_valid facts instructions 243712 1024
    h243712 checked_243712
  have h245760 := Scan.chunk_sound context_valid facts instructions 244736 1024
    h244736 checked_244736
  exact h245760

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
