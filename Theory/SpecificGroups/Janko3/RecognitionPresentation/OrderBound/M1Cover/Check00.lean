module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Tables

/-! Kernel-checked deductions for the literal ATLAS J3G1-P1 subgroup M₁.
Chunks bound the reduction cache; each scan uses previously proved equations. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 4096 in
theorem checked_0 : Scan.checkChunk context facts instructions 0 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_1024 : Scan.checkChunk context facts instructions 1024 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_2048 : Scan.checkChunk context facts instructions 2048 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_3072 : Scan.checkChunk context facts instructions 3072 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_4096 : Scan.checkChunk context facts instructions 4096 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_5120 : Scan.checkChunk context facts instructions 5120 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_6144 : Scan.checkChunk context facts instructions 6144 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_7168 : Scan.checkChunk context facts instructions 7168 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_8192 : Scan.checkChunk context facts instructions 8192 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_9216 : Scan.checkChunk context facts instructions 9216 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_10240 : Scan.checkChunk context facts instructions 10240 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_11264 : Scan.checkChunk context facts instructions 11264 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_12288 : Scan.checkChunk context facts instructions 12288 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_13312 : Scan.checkChunk context facts instructions 13312 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_14336 : Scan.checkChunk context facts instructions 14336 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_15360 : Scan.checkChunk context facts instructions 15360 1024 = true := by
  decide +kernel

theorem sound_0 (prior : ∀ n, n < 0 →
    Holds M1 generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 16384 → Holds M1 generator (definitions.repr generator) (facts n) := by
  have h1024 := Scan.chunk_sound context_valid facts instructions 0 1024
    prior checked_0
  have h2048 := Scan.chunk_sound context_valid facts instructions 1024 1024
    h1024 checked_1024
  have h3072 := Scan.chunk_sound context_valid facts instructions 2048 1024
    h2048 checked_2048
  have h4096 := Scan.chunk_sound context_valid facts instructions 3072 1024
    h3072 checked_3072
  have h5120 := Scan.chunk_sound context_valid facts instructions 4096 1024
    h4096 checked_4096
  have h6144 := Scan.chunk_sound context_valid facts instructions 5120 1024
    h5120 checked_5120
  have h7168 := Scan.chunk_sound context_valid facts instructions 6144 1024
    h6144 checked_6144
  have h8192 := Scan.chunk_sound context_valid facts instructions 7168 1024
    h7168 checked_7168
  have h9216 := Scan.chunk_sound context_valid facts instructions 8192 1024
    h8192 checked_8192
  have h10240 := Scan.chunk_sound context_valid facts instructions 9216 1024
    h9216 checked_9216
  have h11264 := Scan.chunk_sound context_valid facts instructions 10240 1024
    h10240 checked_10240
  have h12288 := Scan.chunk_sound context_valid facts instructions 11264 1024
    h11264 checked_11264
  have h13312 := Scan.chunk_sound context_valid facts instructions 12288 1024
    h12288 checked_12288
  have h14336 := Scan.chunk_sound context_valid facts instructions 13312 1024
    h13312 checked_13312
  have h15360 := Scan.chunk_sound context_valid facts instructions 14336 1024
    h14336 checked_14336
  have h16384 := Scan.chunk_sound context_valid facts instructions 15360 1024
    h15360 checked_15360
  exact h16384

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
