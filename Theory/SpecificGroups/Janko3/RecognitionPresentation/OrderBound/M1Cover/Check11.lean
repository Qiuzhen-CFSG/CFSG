module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Tables

/-! Kernel-checked deductions for the literal ATLAS J3G1-P1 subgroup M₁.
Chunks bound the reduction cache; each scan uses previously proved equations. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 4096 in
theorem checked_180224 : Scan.checkChunk context facts instructions 180224 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_181248 : Scan.checkChunk context facts instructions 181248 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_182272 : Scan.checkChunk context facts instructions 182272 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_183296 : Scan.checkChunk context facts instructions 183296 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_184320 : Scan.checkChunk context facts instructions 184320 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_185344 : Scan.checkChunk context facts instructions 185344 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_186368 : Scan.checkChunk context facts instructions 186368 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_187392 : Scan.checkChunk context facts instructions 187392 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_188416 : Scan.checkChunk context facts instructions 188416 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_189440 : Scan.checkChunk context facts instructions 189440 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_190464 : Scan.checkChunk context facts instructions 190464 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_191488 : Scan.checkChunk context facts instructions 191488 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_192512 : Scan.checkChunk context facts instructions 192512 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_193536 : Scan.checkChunk context facts instructions 193536 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_194560 : Scan.checkChunk context facts instructions 194560 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_195584 : Scan.checkChunk context facts instructions 195584 1024 = true := by
  decide +kernel

theorem sound_180224 (prior : ∀ n, n < 180224 →
    Holds M1 generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 196608 → Holds M1 generator (definitions.repr generator) (facts n) := by
  have h181248 := Scan.chunk_sound context_valid facts instructions 180224 1024
    prior checked_180224
  have h182272 := Scan.chunk_sound context_valid facts instructions 181248 1024
    h181248 checked_181248
  have h183296 := Scan.chunk_sound context_valid facts instructions 182272 1024
    h182272 checked_182272
  have h184320 := Scan.chunk_sound context_valid facts instructions 183296 1024
    h183296 checked_183296
  have h185344 := Scan.chunk_sound context_valid facts instructions 184320 1024
    h184320 checked_184320
  have h186368 := Scan.chunk_sound context_valid facts instructions 185344 1024
    h185344 checked_185344
  have h187392 := Scan.chunk_sound context_valid facts instructions 186368 1024
    h186368 checked_186368
  have h188416 := Scan.chunk_sound context_valid facts instructions 187392 1024
    h187392 checked_187392
  have h189440 := Scan.chunk_sound context_valid facts instructions 188416 1024
    h188416 checked_188416
  have h190464 := Scan.chunk_sound context_valid facts instructions 189440 1024
    h189440 checked_189440
  have h191488 := Scan.chunk_sound context_valid facts instructions 190464 1024
    h190464 checked_190464
  have h192512 := Scan.chunk_sound context_valid facts instructions 191488 1024
    h191488 checked_191488
  have h193536 := Scan.chunk_sound context_valid facts instructions 192512 1024
    h192512 checked_192512
  have h194560 := Scan.chunk_sound context_valid facts instructions 193536 1024
    h193536 checked_193536
  have h195584 := Scan.chunk_sound context_valid facts instructions 194560 1024
    h194560 checked_194560
  have h196608 := Scan.chunk_sound context_valid facts instructions 195584 1024
    h195584 checked_195584
  exact h196608

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
