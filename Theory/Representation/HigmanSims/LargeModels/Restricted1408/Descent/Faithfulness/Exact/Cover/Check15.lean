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
theorem checked_245760 : Scan.checkChunk context facts instructions 245760 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_246272 : Scan.checkChunk context facts instructions 246272 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_246784 : Scan.checkChunk context facts instructions 246784 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_247296 : Scan.checkChunk context facts instructions 247296 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_247808 : Scan.checkChunk context facts instructions 247808 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_248320 : Scan.checkChunk context facts instructions 248320 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_248832 : Scan.checkChunk context facts instructions 248832 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_249344 : Scan.checkChunk context facts instructions 249344 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_249856 : Scan.checkChunk context facts instructions 249856 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_250368 : Scan.checkChunk context facts instructions 250368 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_250880 : Scan.checkChunk context facts instructions 250880 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_251392 : Scan.checkChunk context facts instructions 251392 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_251904 : Scan.checkChunk context facts instructions 251904 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_252416 : Scan.checkChunk context facts instructions 252416 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_252928 : Scan.checkChunk context facts instructions 252928 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_253440 : Scan.checkChunk context facts instructions 253440 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_253952 : Scan.checkChunk context facts instructions 253952 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_254464 : Scan.checkChunk context facts instructions 254464 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_254976 : Scan.checkChunk context facts instructions 254976 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_255488 : Scan.checkChunk context facts instructions 255488 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_256000 : Scan.checkChunk context facts instructions 256000 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_256512 : Scan.checkChunk context facts instructions 256512 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_257024 : Scan.checkChunk context facts instructions 257024 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_257536 : Scan.checkChunk context facts instructions 257536 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_258048 : Scan.checkChunk context facts instructions 258048 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_258560 : Scan.checkChunk context facts instructions 258560 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_259072 : Scan.checkChunk context facts instructions 259072 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_259584 : Scan.checkChunk context facts instructions 259584 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_260096 : Scan.checkChunk context facts instructions 260096 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_260608 : Scan.checkChunk context facts instructions 260608 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_261120 : Scan.checkChunk context facts instructions 261120 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_261632 : Scan.checkChunk context facts instructions 261632 512 = true := by
  decide +kernel

theorem all_hold_262144 (prior : ∀ n, n < 245760 → Holds centralizer certGenerator (definitions.repr certGenerator) (facts n)) : ∀ n, n < 262144 →
    Holds centralizer certGenerator (definitions.repr certGenerator) (facts n) := by
  have h246272 := Scan.chunk_sound context_valid facts instructions 245760 512
    prior checked_245760
  have h246784 := Scan.chunk_sound context_valid facts instructions 246272 512
    h246272 checked_246272
  have h247296 := Scan.chunk_sound context_valid facts instructions 246784 512
    h246784 checked_246784
  have h247808 := Scan.chunk_sound context_valid facts instructions 247296 512
    h247296 checked_247296
  have h248320 := Scan.chunk_sound context_valid facts instructions 247808 512
    h247808 checked_247808
  have h248832 := Scan.chunk_sound context_valid facts instructions 248320 512
    h248320 checked_248320
  have h249344 := Scan.chunk_sound context_valid facts instructions 248832 512
    h248832 checked_248832
  have h249856 := Scan.chunk_sound context_valid facts instructions 249344 512
    h249344 checked_249344
  have h250368 := Scan.chunk_sound context_valid facts instructions 249856 512
    h249856 checked_249856
  have h250880 := Scan.chunk_sound context_valid facts instructions 250368 512
    h250368 checked_250368
  have h251392 := Scan.chunk_sound context_valid facts instructions 250880 512
    h250880 checked_250880
  have h251904 := Scan.chunk_sound context_valid facts instructions 251392 512
    h251392 checked_251392
  have h252416 := Scan.chunk_sound context_valid facts instructions 251904 512
    h251904 checked_251904
  have h252928 := Scan.chunk_sound context_valid facts instructions 252416 512
    h252416 checked_252416
  have h253440 := Scan.chunk_sound context_valid facts instructions 252928 512
    h252928 checked_252928
  have h253952 := Scan.chunk_sound context_valid facts instructions 253440 512
    h253440 checked_253440
  have h254464 := Scan.chunk_sound context_valid facts instructions 253952 512
    h253952 checked_253952
  have h254976 := Scan.chunk_sound context_valid facts instructions 254464 512
    h254464 checked_254464
  have h255488 := Scan.chunk_sound context_valid facts instructions 254976 512
    h254976 checked_254976
  have h256000 := Scan.chunk_sound context_valid facts instructions 255488 512
    h255488 checked_255488
  have h256512 := Scan.chunk_sound context_valid facts instructions 256000 512
    h256000 checked_256000
  have h257024 := Scan.chunk_sound context_valid facts instructions 256512 512
    h256512 checked_256512
  have h257536 := Scan.chunk_sound context_valid facts instructions 257024 512
    h257024 checked_257024
  have h258048 := Scan.chunk_sound context_valid facts instructions 257536 512
    h257536 checked_257536
  have h258560 := Scan.chunk_sound context_valid facts instructions 258048 512
    h258048 checked_258048
  have h259072 := Scan.chunk_sound context_valid facts instructions 258560 512
    h258560 checked_258560
  have h259584 := Scan.chunk_sound context_valid facts instructions 259072 512
    h259072 checked_259072
  have h260096 := Scan.chunk_sound context_valid facts instructions 259584 512
    h259584 checked_259584
  have h260608 := Scan.chunk_sound context_valid facts instructions 260096 512
    h260096 checked_260096
  have h261120 := Scan.chunk_sound context_valid facts instructions 260608 512
    h260608 checked_260608
  have h261632 := Scan.chunk_sound context_valid facts instructions 261120 512
    h261120 checked_261120
  have h262144 := Scan.chunk_sound context_valid facts instructions 261632 512
    h261632 checked_261632
  exact h262144

end Sporadic.LeechRelated.HS.AtlasPresentation.Exact.Cover
