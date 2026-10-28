module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Tables

/-! Kernel-checked deductions for the literal ATLAS J3G1-P1 subgroup M₁.
Chunks bound the reduction cache; each scan uses previously proved equations. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 4096 in
theorem checked_212992 : Scan.checkChunk context facts instructions 212992 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_214016 : Scan.checkChunk context facts instructions 214016 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_215040 : Scan.checkChunk context facts instructions 215040 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_216064 : Scan.checkChunk context facts instructions 216064 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_217088 : Scan.checkChunk context facts instructions 217088 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_218112 : Scan.checkChunk context facts instructions 218112 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_219136 : Scan.checkChunk context facts instructions 219136 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_220160 : Scan.checkChunk context facts instructions 220160 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_221184 : Scan.checkChunk context facts instructions 221184 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_222208 : Scan.checkChunk context facts instructions 222208 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_223232 : Scan.checkChunk context facts instructions 223232 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_224256 : Scan.checkChunk context facts instructions 224256 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_225280 : Scan.checkChunk context facts instructions 225280 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_226304 : Scan.checkChunk context facts instructions 226304 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_227328 : Scan.checkChunk context facts instructions 227328 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_228352 : Scan.checkChunk context facts instructions 228352 1024 = true := by
  decide +kernel

theorem sound_212992 (prior : ∀ n, n < 212992 →
    Holds M1 generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 229376 → Holds M1 generator (definitions.repr generator) (facts n) := by
  have h214016 := Scan.chunk_sound context_valid facts instructions 212992 1024
    prior checked_212992
  have h215040 := Scan.chunk_sound context_valid facts instructions 214016 1024
    h214016 checked_214016
  have h216064 := Scan.chunk_sound context_valid facts instructions 215040 1024
    h215040 checked_215040
  have h217088 := Scan.chunk_sound context_valid facts instructions 216064 1024
    h216064 checked_216064
  have h218112 := Scan.chunk_sound context_valid facts instructions 217088 1024
    h217088 checked_217088
  have h219136 := Scan.chunk_sound context_valid facts instructions 218112 1024
    h218112 checked_218112
  have h220160 := Scan.chunk_sound context_valid facts instructions 219136 1024
    h219136 checked_219136
  have h221184 := Scan.chunk_sound context_valid facts instructions 220160 1024
    h220160 checked_220160
  have h222208 := Scan.chunk_sound context_valid facts instructions 221184 1024
    h221184 checked_221184
  have h223232 := Scan.chunk_sound context_valid facts instructions 222208 1024
    h222208 checked_222208
  have h224256 := Scan.chunk_sound context_valid facts instructions 223232 1024
    h223232 checked_223232
  have h225280 := Scan.chunk_sound context_valid facts instructions 224256 1024
    h224256 checked_224256
  have h226304 := Scan.chunk_sound context_valid facts instructions 225280 1024
    h225280 checked_225280
  have h227328 := Scan.chunk_sound context_valid facts instructions 226304 1024
    h226304 checked_226304
  have h228352 := Scan.chunk_sound context_valid facts instructions 227328 1024
    h227328 checked_227328
  have h229376 := Scan.chunk_sound context_valid facts instructions 228352 1024
    h228352 checked_228352
  exact h229376

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
