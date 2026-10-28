module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Tables

/-! Kernel-checked deductions for the literal ATLAS J3G1-P1 subgroup M₁.
Chunks bound the reduction cache; each scan uses previously proved equations. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 4096 in
theorem checked_114688 : Scan.checkChunk context facts instructions 114688 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_115712 : Scan.checkChunk context facts instructions 115712 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_116736 : Scan.checkChunk context facts instructions 116736 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_117760 : Scan.checkChunk context facts instructions 117760 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_118784 : Scan.checkChunk context facts instructions 118784 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_119808 : Scan.checkChunk context facts instructions 119808 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_120832 : Scan.checkChunk context facts instructions 120832 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_121856 : Scan.checkChunk context facts instructions 121856 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_122880 : Scan.checkChunk context facts instructions 122880 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_123904 : Scan.checkChunk context facts instructions 123904 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_124928 : Scan.checkChunk context facts instructions 124928 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_125952 : Scan.checkChunk context facts instructions 125952 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_126976 : Scan.checkChunk context facts instructions 126976 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_128000 : Scan.checkChunk context facts instructions 128000 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_129024 : Scan.checkChunk context facts instructions 129024 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_130048 : Scan.checkChunk context facts instructions 130048 1024 = true := by
  decide +kernel

theorem sound_114688 (prior : ∀ n, n < 114688 →
    Holds M1 generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 131072 → Holds M1 generator (definitions.repr generator) (facts n) := by
  have h115712 := Scan.chunk_sound context_valid facts instructions 114688 1024
    prior checked_114688
  have h116736 := Scan.chunk_sound context_valid facts instructions 115712 1024
    h115712 checked_115712
  have h117760 := Scan.chunk_sound context_valid facts instructions 116736 1024
    h116736 checked_116736
  have h118784 := Scan.chunk_sound context_valid facts instructions 117760 1024
    h117760 checked_117760
  have h119808 := Scan.chunk_sound context_valid facts instructions 118784 1024
    h118784 checked_118784
  have h120832 := Scan.chunk_sound context_valid facts instructions 119808 1024
    h119808 checked_119808
  have h121856 := Scan.chunk_sound context_valid facts instructions 120832 1024
    h120832 checked_120832
  have h122880 := Scan.chunk_sound context_valid facts instructions 121856 1024
    h121856 checked_121856
  have h123904 := Scan.chunk_sound context_valid facts instructions 122880 1024
    h122880 checked_122880
  have h124928 := Scan.chunk_sound context_valid facts instructions 123904 1024
    h123904 checked_123904
  have h125952 := Scan.chunk_sound context_valid facts instructions 124928 1024
    h124928 checked_124928
  have h126976 := Scan.chunk_sound context_valid facts instructions 125952 1024
    h125952 checked_125952
  have h128000 := Scan.chunk_sound context_valid facts instructions 126976 1024
    h126976 checked_126976
  have h129024 := Scan.chunk_sound context_valid facts instructions 128000 1024
    h128000 checked_128000
  have h130048 := Scan.chunk_sound context_valid facts instructions 129024 1024
    h129024 checked_129024
  have h131072 := Scan.chunk_sound context_valid facts instructions 130048 1024
    h130048 checked_130048
  exact h131072

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
