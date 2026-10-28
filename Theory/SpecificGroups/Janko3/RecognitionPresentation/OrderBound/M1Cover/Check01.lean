module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Tables

/-! Kernel-checked deductions for the literal ATLAS J3G1-P1 subgroup M₁.
Chunks bound the reduction cache; each scan uses previously proved equations. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 4096 in
theorem checked_16384 : Scan.checkChunk context facts instructions 16384 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_17408 : Scan.checkChunk context facts instructions 17408 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_18432 : Scan.checkChunk context facts instructions 18432 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_19456 : Scan.checkChunk context facts instructions 19456 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_20480 : Scan.checkChunk context facts instructions 20480 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_21504 : Scan.checkChunk context facts instructions 21504 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_22528 : Scan.checkChunk context facts instructions 22528 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_23552 : Scan.checkChunk context facts instructions 23552 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_24576 : Scan.checkChunk context facts instructions 24576 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_25600 : Scan.checkChunk context facts instructions 25600 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_26624 : Scan.checkChunk context facts instructions 26624 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_27648 : Scan.checkChunk context facts instructions 27648 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_28672 : Scan.checkChunk context facts instructions 28672 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_29696 : Scan.checkChunk context facts instructions 29696 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_30720 : Scan.checkChunk context facts instructions 30720 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_31744 : Scan.checkChunk context facts instructions 31744 1024 = true := by
  decide +kernel

theorem sound_16384 (prior : ∀ n, n < 16384 →
    Holds M1 generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 32768 → Holds M1 generator (definitions.repr generator) (facts n) := by
  have h17408 := Scan.chunk_sound context_valid facts instructions 16384 1024
    prior checked_16384
  have h18432 := Scan.chunk_sound context_valid facts instructions 17408 1024
    h17408 checked_17408
  have h19456 := Scan.chunk_sound context_valid facts instructions 18432 1024
    h18432 checked_18432
  have h20480 := Scan.chunk_sound context_valid facts instructions 19456 1024
    h19456 checked_19456
  have h21504 := Scan.chunk_sound context_valid facts instructions 20480 1024
    h20480 checked_20480
  have h22528 := Scan.chunk_sound context_valid facts instructions 21504 1024
    h21504 checked_21504
  have h23552 := Scan.chunk_sound context_valid facts instructions 22528 1024
    h22528 checked_22528
  have h24576 := Scan.chunk_sound context_valid facts instructions 23552 1024
    h23552 checked_23552
  have h25600 := Scan.chunk_sound context_valid facts instructions 24576 1024
    h24576 checked_24576
  have h26624 := Scan.chunk_sound context_valid facts instructions 25600 1024
    h25600 checked_25600
  have h27648 := Scan.chunk_sound context_valid facts instructions 26624 1024
    h26624 checked_26624
  have h28672 := Scan.chunk_sound context_valid facts instructions 27648 1024
    h27648 checked_27648
  have h29696 := Scan.chunk_sound context_valid facts instructions 28672 1024
    h28672 checked_28672
  have h30720 := Scan.chunk_sound context_valid facts instructions 29696 1024
    h29696 checked_29696
  have h31744 := Scan.chunk_sound context_valid facts instructions 30720 1024
    h30720 checked_30720
  have h32768 := Scan.chunk_sound context_valid facts instructions 31744 1024
    h31744 checked_31744
  exact h32768

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
