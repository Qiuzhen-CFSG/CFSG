module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.M1aBound.FiniteBound.Reduced.Bound.LocalFinite.CertificateData

/-! Kernel checks for the conditional local coset certificate.
Each accepted step is an actual word deduction. The four relator identities
remain explicit premises; see `source/README.md`. -/

@[expose] public section
namespace Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced.Bound.LocalFinite.Certificate
open Subgroup.CosetWordCertificate

theorem checked_0 : Scan.checkChunk context facts instructions 0 128 = true := by
  decide +kernel

theorem checked_128 : Scan.checkChunk context facts instructions 128 128 = true := by
  decide +kernel

theorem checked_256 : Scan.checkChunk context facts instructions 256 128 = true := by
  decide +kernel

theorem checked_384 : Scan.checkChunk context facts instructions 384 128 = true := by
  decide +kernel

theorem checked_512 : Scan.checkChunk context facts instructions 512 128 = true := by
  decide +kernel

theorem checked_640 : Scan.checkChunk context facts instructions 640 128 = true := by
  decide +kernel

theorem checked_768 : Scan.checkChunk context facts instructions 768 128 = true := by
  decide +kernel

theorem checked_896 : Scan.checkChunk context facts instructions 896 128 = true := by
  decide +kernel

theorem checked_1024 : Scan.checkChunk context facts instructions 1024 128 = true := by
  decide +kernel

theorem checked_1152 : Scan.checkChunk context facts instructions 1152 128 = true := by
  decide +kernel

theorem checked_1280 : Scan.checkChunk context facts instructions 1280 128 = true := by
  decide +kernel

theorem checked_1408 : Scan.checkChunk context facts instructions 1408 128 = true := by
  decide +kernel

theorem checked_1536 : Scan.checkChunk context facts instructions 1536 128 = true := by
  decide +kernel

theorem checked_1664 : Scan.checkChunk context facts instructions 1664 128 = true := by
  decide +kernel

theorem checked_1792 : Scan.checkChunk context facts instructions 1792 128 = true := by
  decide +kernel

theorem checked_1920 : Scan.checkChunk context facts instructions 1920 128 = true := by
  decide +kernel

theorem checked_2048 : Scan.checkChunk context facts instructions 2048 128 = true := by
  decide +kernel

theorem checked_2176 : Scan.checkChunk context facts instructions 2176 128 = true := by
  decide +kernel

theorem checked_2304 : Scan.checkChunk context facts instructions 2304 128 = true := by
  decide +kernel

theorem checked_2432 : Scan.checkChunk context facts instructions 2432 128 = true := by
  decide +kernel

theorem checked_2560 : Scan.checkChunk context facts instructions 2560 128 = true := by
  decide +kernel

theorem checked_2688 : Scan.checkChunk context facts instructions 2688 128 = true := by
  decide +kernel

theorem checked_2816 : Scan.checkChunk context facts instructions 2816 128 = true := by
  decide +kernel

theorem checked_2944 : Scan.checkChunk context facts instructions 2944 128 = true := by
  decide +kernel

theorem checked_3072 : Scan.checkChunk context facts instructions 3072 128 = true := by
  decide +kernel

theorem checked_3200 : Scan.checkChunk context facts instructions 3200 128 = true := by
  decide +kernel

theorem checked_3328 : Scan.checkChunk context facts instructions 3328 128 = true := by
  decide +kernel

theorem checked_3456 : Scan.checkChunk context facts instructions 3456 128 = true := by
  decide +kernel

theorem checked_3584 : Scan.checkChunk context facts instructions 3584 128 = true := by
  decide +kernel

theorem checked_3712 : Scan.checkChunk context facts instructions 3712 128 = true := by
  decide +kernel

theorem checked_3840 : Scan.checkChunk context facts instructions 3840 128 = true := by
  decide +kernel

theorem checked_3968 : Scan.checkChunk context facts instructions 3968 128 = true := by
  decide +kernel

theorem holds_4096 (hr : ∀ r : Fin 4, eval subgroupGenerator (extraRelatorWord r) = 1) :
    ∀ n, n < 4096 → Holds smallSubgroup subgroupGenerator (definitions.repr subgroupGenerator) (facts n) := by
  have h128 := Scan.chunk_sound (context_valid hr) facts instructions
    0 128 (fun n hn => (Nat.not_lt_zero n hn).elim) checked_0
  have h256 := Scan.chunk_sound (context_valid hr) facts instructions
    128 128 h128 checked_128
  have h384 := Scan.chunk_sound (context_valid hr) facts instructions
    256 128 h256 checked_256
  have h512 := Scan.chunk_sound (context_valid hr) facts instructions
    384 128 h384 checked_384
  have h640 := Scan.chunk_sound (context_valid hr) facts instructions
    512 128 h512 checked_512
  have h768 := Scan.chunk_sound (context_valid hr) facts instructions
    640 128 h640 checked_640
  have h896 := Scan.chunk_sound (context_valid hr) facts instructions
    768 128 h768 checked_768
  have h1024 := Scan.chunk_sound (context_valid hr) facts instructions
    896 128 h896 checked_896
  have h1152 := Scan.chunk_sound (context_valid hr) facts instructions
    1024 128 h1024 checked_1024
  have h1280 := Scan.chunk_sound (context_valid hr) facts instructions
    1152 128 h1152 checked_1152
  have h1408 := Scan.chunk_sound (context_valid hr) facts instructions
    1280 128 h1280 checked_1280
  have h1536 := Scan.chunk_sound (context_valid hr) facts instructions
    1408 128 h1408 checked_1408
  have h1664 := Scan.chunk_sound (context_valid hr) facts instructions
    1536 128 h1536 checked_1536
  have h1792 := Scan.chunk_sound (context_valid hr) facts instructions
    1664 128 h1664 checked_1664
  have h1920 := Scan.chunk_sound (context_valid hr) facts instructions
    1792 128 h1792 checked_1792
  have h2048 := Scan.chunk_sound (context_valid hr) facts instructions
    1920 128 h1920 checked_1920
  have h2176 := Scan.chunk_sound (context_valid hr) facts instructions
    2048 128 h2048 checked_2048
  have h2304 := Scan.chunk_sound (context_valid hr) facts instructions
    2176 128 h2176 checked_2176
  have h2432 := Scan.chunk_sound (context_valid hr) facts instructions
    2304 128 h2304 checked_2304
  have h2560 := Scan.chunk_sound (context_valid hr) facts instructions
    2432 128 h2432 checked_2432
  have h2688 := Scan.chunk_sound (context_valid hr) facts instructions
    2560 128 h2560 checked_2560
  have h2816 := Scan.chunk_sound (context_valid hr) facts instructions
    2688 128 h2688 checked_2688
  have h2944 := Scan.chunk_sound (context_valid hr) facts instructions
    2816 128 h2816 checked_2816
  have h3072 := Scan.chunk_sound (context_valid hr) facts instructions
    2944 128 h2944 checked_2944
  have h3200 := Scan.chunk_sound (context_valid hr) facts instructions
    3072 128 h3072 checked_3072
  have h3328 := Scan.chunk_sound (context_valid hr) facts instructions
    3200 128 h3200 checked_3200
  have h3456 := Scan.chunk_sound (context_valid hr) facts instructions
    3328 128 h3328 checked_3328
  have h3584 := Scan.chunk_sound (context_valid hr) facts instructions
    3456 128 h3456 checked_3456
  have h3712 := Scan.chunk_sound (context_valid hr) facts instructions
    3584 128 h3584 checked_3584
  have h3840 := Scan.chunk_sound (context_valid hr) facts instructions
    3712 128 h3712 checked_3712
  have h3968 := Scan.chunk_sound (context_valid hr) facts instructions
    3840 128 h3840 checked_3840
  have h4096 := Scan.chunk_sound (context_valid hr) facts instructions
    3968 128 h3968 checked_3968
  exact h4096

end Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced.Bound.LocalFinite.Certificate
