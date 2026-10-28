module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Tables

/-! Kernel-checked deductions for the literal ATLAS J3G1-P1 subgroup M₁.
Chunks bound the reduction cache; each scan uses previously proved equations. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 4096 in
theorem checked_49152 : Scan.checkChunk context facts instructions 49152 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_50176 : Scan.checkChunk context facts instructions 50176 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_51200 : Scan.checkChunk context facts instructions 51200 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_52224 : Scan.checkChunk context facts instructions 52224 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_53248 : Scan.checkChunk context facts instructions 53248 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_54272 : Scan.checkChunk context facts instructions 54272 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_55296 : Scan.checkChunk context facts instructions 55296 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_56320 : Scan.checkChunk context facts instructions 56320 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_57344 : Scan.checkChunk context facts instructions 57344 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_58368 : Scan.checkChunk context facts instructions 58368 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_59392 : Scan.checkChunk context facts instructions 59392 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_60416 : Scan.checkChunk context facts instructions 60416 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_61440 : Scan.checkChunk context facts instructions 61440 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_62464 : Scan.checkChunk context facts instructions 62464 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_63488 : Scan.checkChunk context facts instructions 63488 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_64512 : Scan.checkChunk context facts instructions 64512 1024 = true := by
  decide +kernel

theorem sound_49152 (prior : ∀ n, n < 49152 →
    Holds M1 generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 65536 → Holds M1 generator (definitions.repr generator) (facts n) := by
  have h50176 := Scan.chunk_sound context_valid facts instructions 49152 1024
    prior checked_49152
  have h51200 := Scan.chunk_sound context_valid facts instructions 50176 1024
    h50176 checked_50176
  have h52224 := Scan.chunk_sound context_valid facts instructions 51200 1024
    h51200 checked_51200
  have h53248 := Scan.chunk_sound context_valid facts instructions 52224 1024
    h52224 checked_52224
  have h54272 := Scan.chunk_sound context_valid facts instructions 53248 1024
    h53248 checked_53248
  have h55296 := Scan.chunk_sound context_valid facts instructions 54272 1024
    h54272 checked_54272
  have h56320 := Scan.chunk_sound context_valid facts instructions 55296 1024
    h55296 checked_55296
  have h57344 := Scan.chunk_sound context_valid facts instructions 56320 1024
    h56320 checked_56320
  have h58368 := Scan.chunk_sound context_valid facts instructions 57344 1024
    h57344 checked_57344
  have h59392 := Scan.chunk_sound context_valid facts instructions 58368 1024
    h58368 checked_58368
  have h60416 := Scan.chunk_sound context_valid facts instructions 59392 1024
    h59392 checked_59392
  have h61440 := Scan.chunk_sound context_valid facts instructions 60416 1024
    h60416 checked_60416
  have h62464 := Scan.chunk_sound context_valid facts instructions 61440 1024
    h61440 checked_61440
  have h63488 := Scan.chunk_sound context_valid facts instructions 62464 1024
    h62464 checked_62464
  have h64512 := Scan.chunk_sound context_valid facts instructions 63488 1024
    h63488 checked_63488
  have h65536 := Scan.chunk_sound context_valid facts instructions 64512 1024
    h64512 checked_64512
  exact h65536

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
