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
theorem checked_0 : Scan.checkChunk context facts instructions 0 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_512 : Scan.checkChunk context facts instructions 512 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_1024 : Scan.checkChunk context facts instructions 1024 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_1536 : Scan.checkChunk context facts instructions 1536 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_2048 : Scan.checkChunk context facts instructions 2048 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_2560 : Scan.checkChunk context facts instructions 2560 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_3072 : Scan.checkChunk context facts instructions 3072 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_3584 : Scan.checkChunk context facts instructions 3584 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_4096 : Scan.checkChunk context facts instructions 4096 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_4608 : Scan.checkChunk context facts instructions 4608 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_5120 : Scan.checkChunk context facts instructions 5120 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_5632 : Scan.checkChunk context facts instructions 5632 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_6144 : Scan.checkChunk context facts instructions 6144 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_6656 : Scan.checkChunk context facts instructions 6656 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_7168 : Scan.checkChunk context facts instructions 7168 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_7680 : Scan.checkChunk context facts instructions 7680 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_8192 : Scan.checkChunk context facts instructions 8192 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_8704 : Scan.checkChunk context facts instructions 8704 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_9216 : Scan.checkChunk context facts instructions 9216 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_9728 : Scan.checkChunk context facts instructions 9728 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_10240 : Scan.checkChunk context facts instructions 10240 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_10752 : Scan.checkChunk context facts instructions 10752 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_11264 : Scan.checkChunk context facts instructions 11264 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_11776 : Scan.checkChunk context facts instructions 11776 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_12288 : Scan.checkChunk context facts instructions 12288 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_12800 : Scan.checkChunk context facts instructions 12800 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_13312 : Scan.checkChunk context facts instructions 13312 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_13824 : Scan.checkChunk context facts instructions 13824 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_14336 : Scan.checkChunk context facts instructions 14336 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_14848 : Scan.checkChunk context facts instructions 14848 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_15360 : Scan.checkChunk context facts instructions 15360 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_15872 : Scan.checkChunk context facts instructions 15872 512 = true := by
  decide +kernel

theorem all_hold_16384 : ∀ n, n < 16384 →
    Holds centralizer certGenerator (definitions.repr certGenerator) (facts n) := by
  have h512 := Scan.chunk_sound context_valid facts instructions 0 512
    (fun n hn => (Nat.not_lt_zero n hn).elim) checked_0
  have h1024 := Scan.chunk_sound context_valid facts instructions 512 512
    h512 checked_512
  have h1536 := Scan.chunk_sound context_valid facts instructions 1024 512
    h1024 checked_1024
  have h2048 := Scan.chunk_sound context_valid facts instructions 1536 512
    h1536 checked_1536
  have h2560 := Scan.chunk_sound context_valid facts instructions 2048 512
    h2048 checked_2048
  have h3072 := Scan.chunk_sound context_valid facts instructions 2560 512
    h2560 checked_2560
  have h3584 := Scan.chunk_sound context_valid facts instructions 3072 512
    h3072 checked_3072
  have h4096 := Scan.chunk_sound context_valid facts instructions 3584 512
    h3584 checked_3584
  have h4608 := Scan.chunk_sound context_valid facts instructions 4096 512
    h4096 checked_4096
  have h5120 := Scan.chunk_sound context_valid facts instructions 4608 512
    h4608 checked_4608
  have h5632 := Scan.chunk_sound context_valid facts instructions 5120 512
    h5120 checked_5120
  have h6144 := Scan.chunk_sound context_valid facts instructions 5632 512
    h5632 checked_5632
  have h6656 := Scan.chunk_sound context_valid facts instructions 6144 512
    h6144 checked_6144
  have h7168 := Scan.chunk_sound context_valid facts instructions 6656 512
    h6656 checked_6656
  have h7680 := Scan.chunk_sound context_valid facts instructions 7168 512
    h7168 checked_7168
  have h8192 := Scan.chunk_sound context_valid facts instructions 7680 512
    h7680 checked_7680
  have h8704 := Scan.chunk_sound context_valid facts instructions 8192 512
    h8192 checked_8192
  have h9216 := Scan.chunk_sound context_valid facts instructions 8704 512
    h8704 checked_8704
  have h9728 := Scan.chunk_sound context_valid facts instructions 9216 512
    h9216 checked_9216
  have h10240 := Scan.chunk_sound context_valid facts instructions 9728 512
    h9728 checked_9728
  have h10752 := Scan.chunk_sound context_valid facts instructions 10240 512
    h10240 checked_10240
  have h11264 := Scan.chunk_sound context_valid facts instructions 10752 512
    h10752 checked_10752
  have h11776 := Scan.chunk_sound context_valid facts instructions 11264 512
    h11264 checked_11264
  have h12288 := Scan.chunk_sound context_valid facts instructions 11776 512
    h11776 checked_11776
  have h12800 := Scan.chunk_sound context_valid facts instructions 12288 512
    h12288 checked_12288
  have h13312 := Scan.chunk_sound context_valid facts instructions 12800 512
    h12800 checked_12800
  have h13824 := Scan.chunk_sound context_valid facts instructions 13312 512
    h13312 checked_13312
  have h14336 := Scan.chunk_sound context_valid facts instructions 13824 512
    h13824 checked_13824
  have h14848 := Scan.chunk_sound context_valid facts instructions 14336 512
    h14336 checked_14336
  have h15360 := Scan.chunk_sound context_valid facts instructions 14848 512
    h14848 checked_14848
  have h15872 := Scan.chunk_sound context_valid facts instructions 15360 512
    h15360 checked_15360
  have h16384 := Scan.chunk_sound context_valid facts instructions 15872 512
    h15872 checked_15872
  exact h16384

end Sporadic.LeechRelated.HS.AtlasPresentation.Exact.Cover
