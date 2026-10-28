module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Tables

/-! Kernel-checked deductions for the literal ATLAS J3G1-P1 subgroup M₁.
Chunks bound the reduction cache; each scan uses previously proved equations. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 4096 in
theorem checked_163840 : Scan.checkChunk context facts instructions 163840 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_164864 : Scan.checkChunk context facts instructions 164864 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_165888 : Scan.checkChunk context facts instructions 165888 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_166912 : Scan.checkChunk context facts instructions 166912 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_167936 : Scan.checkChunk context facts instructions 167936 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_168960 : Scan.checkChunk context facts instructions 168960 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_169984 : Scan.checkChunk context facts instructions 169984 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_171008 : Scan.checkChunk context facts instructions 171008 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_172032 : Scan.checkChunk context facts instructions 172032 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_173056 : Scan.checkChunk context facts instructions 173056 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_174080 : Scan.checkChunk context facts instructions 174080 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_175104 : Scan.checkChunk context facts instructions 175104 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_176128 : Scan.checkChunk context facts instructions 176128 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_177152 : Scan.checkChunk context facts instructions 177152 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_178176 : Scan.checkChunk context facts instructions 178176 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_179200 : Scan.checkChunk context facts instructions 179200 1024 = true := by
  decide +kernel

theorem sound_163840 (prior : ∀ n, n < 163840 →
    Holds M1 generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 180224 → Holds M1 generator (definitions.repr generator) (facts n) := by
  have h164864 := Scan.chunk_sound context_valid facts instructions 163840 1024
    prior checked_163840
  have h165888 := Scan.chunk_sound context_valid facts instructions 164864 1024
    h164864 checked_164864
  have h166912 := Scan.chunk_sound context_valid facts instructions 165888 1024
    h165888 checked_165888
  have h167936 := Scan.chunk_sound context_valid facts instructions 166912 1024
    h166912 checked_166912
  have h168960 := Scan.chunk_sound context_valid facts instructions 167936 1024
    h167936 checked_167936
  have h169984 := Scan.chunk_sound context_valid facts instructions 168960 1024
    h168960 checked_168960
  have h171008 := Scan.chunk_sound context_valid facts instructions 169984 1024
    h169984 checked_169984
  have h172032 := Scan.chunk_sound context_valid facts instructions 171008 1024
    h171008 checked_171008
  have h173056 := Scan.chunk_sound context_valid facts instructions 172032 1024
    h172032 checked_172032
  have h174080 := Scan.chunk_sound context_valid facts instructions 173056 1024
    h173056 checked_173056
  have h175104 := Scan.chunk_sound context_valid facts instructions 174080 1024
    h174080 checked_174080
  have h176128 := Scan.chunk_sound context_valid facts instructions 175104 1024
    h175104 checked_175104
  have h177152 := Scan.chunk_sound context_valid facts instructions 176128 1024
    h176128 checked_176128
  have h178176 := Scan.chunk_sound context_valid facts instructions 177152 1024
    h177152 checked_177152
  have h179200 := Scan.chunk_sound context_valid facts instructions 178176 1024
    h178176 checked_178176
  have h180224 := Scan.chunk_sound context_valid facts instructions 179200 1024
    h179200 checked_179200
  exact h180224

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
