module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Tables

/-! Kernel-checked deductions for the literal ATLAS J3G1-P1 subgroup M₁.
Chunks bound the reduction cache; each scan uses previously proved equations. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 4096 in
theorem checked_245760 : Scan.checkChunk context facts instructions 245760 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_246784 : Scan.checkChunk context facts instructions 246784 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_247808 : Scan.checkChunk context facts instructions 247808 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_248832 : Scan.checkChunk context facts instructions 248832 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_249856 : Scan.checkChunk context facts instructions 249856 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_250880 : Scan.checkChunk context facts instructions 250880 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_251904 : Scan.checkChunk context facts instructions 251904 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_252928 : Scan.checkChunk context facts instructions 252928 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_253952 : Scan.checkChunk context facts instructions 253952 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_254976 : Scan.checkChunk context facts instructions 254976 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_256000 : Scan.checkChunk context facts instructions 256000 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_257024 : Scan.checkChunk context facts instructions 257024 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_258048 : Scan.checkChunk context facts instructions 258048 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_259072 : Scan.checkChunk context facts instructions 259072 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_260096 : Scan.checkChunk context facts instructions 260096 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_261120 : Scan.checkChunk context facts instructions 261120 1024 = true := by
  decide +kernel

theorem sound_245760 (prior : ∀ n, n < 245760 →
    Holds M1 generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 262144 → Holds M1 generator (definitions.repr generator) (facts n) := by
  have h246784 := Scan.chunk_sound context_valid facts instructions 245760 1024
    prior checked_245760
  have h247808 := Scan.chunk_sound context_valid facts instructions 246784 1024
    h246784 checked_246784
  have h248832 := Scan.chunk_sound context_valid facts instructions 247808 1024
    h247808 checked_247808
  have h249856 := Scan.chunk_sound context_valid facts instructions 248832 1024
    h248832 checked_248832
  have h250880 := Scan.chunk_sound context_valid facts instructions 249856 1024
    h249856 checked_249856
  have h251904 := Scan.chunk_sound context_valid facts instructions 250880 1024
    h250880 checked_250880
  have h252928 := Scan.chunk_sound context_valid facts instructions 251904 1024
    h251904 checked_251904
  have h253952 := Scan.chunk_sound context_valid facts instructions 252928 1024
    h252928 checked_252928
  have h254976 := Scan.chunk_sound context_valid facts instructions 253952 1024
    h253952 checked_253952
  have h256000 := Scan.chunk_sound context_valid facts instructions 254976 1024
    h254976 checked_254976
  have h257024 := Scan.chunk_sound context_valid facts instructions 256000 1024
    h256000 checked_256000
  have h258048 := Scan.chunk_sound context_valid facts instructions 257024 1024
    h257024 checked_257024
  have h259072 := Scan.chunk_sound context_valid facts instructions 258048 1024
    h258048 checked_258048
  have h260096 := Scan.chunk_sound context_valid facts instructions 259072 1024
    h259072 checked_259072
  have h261120 := Scan.chunk_sound context_valid facts instructions 260096 1024
    h260096 checked_260096
  have h262144 := Scan.chunk_sound context_valid facts instructions 261120 1024
    h261120 checked_261120
  exact h262144

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
