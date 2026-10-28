module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.M1aBound.FiniteBound.Reduced.Bound.LocalFinite.Checks11

/-! Kernel checks for the conditional local coset certificate.
Each accepted step is an actual word deduction. The four relator identities
remain explicit premises; see `source/README.md`. -/

@[expose] public section
namespace Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced.Bound.LocalFinite.Certificate
open Subgroup.CosetWordCertificate

theorem checked_49152 : Scan.checkChunk context facts instructions 49152 128 = true := by
  decide +kernel

theorem checked_49280 : Scan.checkChunk context facts instructions 49280 128 = true := by
  decide +kernel

theorem checked_49408 : Scan.checkChunk context facts instructions 49408 128 = true := by
  decide +kernel

theorem checked_49536 : Scan.checkChunk context facts instructions 49536 128 = true := by
  decide +kernel

theorem checked_49664 : Scan.checkChunk context facts instructions 49664 128 = true := by
  decide +kernel

theorem checked_49792 : Scan.checkChunk context facts instructions 49792 128 = true := by
  decide +kernel

theorem checked_49920 : Scan.checkChunk context facts instructions 49920 128 = true := by
  decide +kernel

theorem checked_50048 : Scan.checkChunk context facts instructions 50048 128 = true := by
  decide +kernel

theorem checked_50176 : Scan.checkChunk context facts instructions 50176 128 = true := by
  decide +kernel

theorem checked_50304 : Scan.checkChunk context facts instructions 50304 128 = true := by
  decide +kernel

theorem checked_50432 : Scan.checkChunk context facts instructions 50432 128 = true := by
  decide +kernel

theorem checked_50560 : Scan.checkChunk context facts instructions 50560 128 = true := by
  decide +kernel

theorem checked_50688 : Scan.checkChunk context facts instructions 50688 128 = true := by
  decide +kernel

theorem checked_50816 : Scan.checkChunk context facts instructions 50816 128 = true := by
  decide +kernel

theorem checked_50944 : Scan.checkChunk context facts instructions 50944 128 = true := by
  decide +kernel

theorem checked_51072 : Scan.checkChunk context facts instructions 51072 128 = true := by
  decide +kernel

theorem checked_51200 : Scan.checkChunk context facts instructions 51200 128 = true := by
  decide +kernel

theorem checked_51328 : Scan.checkChunk context facts instructions 51328 128 = true := by
  decide +kernel

theorem checked_51456 : Scan.checkChunk context facts instructions 51456 128 = true := by
  decide +kernel

theorem checked_51584 : Scan.checkChunk context facts instructions 51584 128 = true := by
  decide +kernel

theorem checked_51712 : Scan.checkChunk context facts instructions 51712 128 = true := by
  decide +kernel

theorem checked_51840 : Scan.checkChunk context facts instructions 51840 128 = true := by
  decide +kernel

theorem checked_51968 : Scan.checkChunk context facts instructions 51968 128 = true := by
  decide +kernel

theorem checked_52096 : Scan.checkChunk context facts instructions 52096 128 = true := by
  decide +kernel

theorem checked_52224 : Scan.checkChunk context facts instructions 52224 128 = true := by
  decide +kernel

theorem checked_52352 : Scan.checkChunk context facts instructions 52352 128 = true := by
  decide +kernel

theorem checked_52480 : Scan.checkChunk context facts instructions 52480 128 = true := by
  decide +kernel

theorem checked_52608 : Scan.checkChunk context facts instructions 52608 128 = true := by
  decide +kernel

theorem checked_52736 : Scan.checkChunk context facts instructions 52736 128 = true := by
  decide +kernel

theorem checked_52864 : Scan.checkChunk context facts instructions 52864 128 = true := by
  decide +kernel

theorem checked_52992 : Scan.checkChunk context facts instructions 52992 128 = true := by
  decide +kernel

theorem checked_53120 : Scan.checkChunk context facts instructions 53120 128 = true := by
  decide +kernel

theorem holds_53248 (hr : ∀ r : Fin 4, eval subgroupGenerator (extraRelatorWord r) = 1) :
    ∀ n, n < 53248 → Holds smallSubgroup subgroupGenerator (definitions.repr subgroupGenerator) (facts n) := by
  have h49280 := Scan.chunk_sound (context_valid hr) facts instructions
    49152 128 (holds_49152 hr) checked_49152
  have h49408 := Scan.chunk_sound (context_valid hr) facts instructions
    49280 128 h49280 checked_49280
  have h49536 := Scan.chunk_sound (context_valid hr) facts instructions
    49408 128 h49408 checked_49408
  have h49664 := Scan.chunk_sound (context_valid hr) facts instructions
    49536 128 h49536 checked_49536
  have h49792 := Scan.chunk_sound (context_valid hr) facts instructions
    49664 128 h49664 checked_49664
  have h49920 := Scan.chunk_sound (context_valid hr) facts instructions
    49792 128 h49792 checked_49792
  have h50048 := Scan.chunk_sound (context_valid hr) facts instructions
    49920 128 h49920 checked_49920
  have h50176 := Scan.chunk_sound (context_valid hr) facts instructions
    50048 128 h50048 checked_50048
  have h50304 := Scan.chunk_sound (context_valid hr) facts instructions
    50176 128 h50176 checked_50176
  have h50432 := Scan.chunk_sound (context_valid hr) facts instructions
    50304 128 h50304 checked_50304
  have h50560 := Scan.chunk_sound (context_valid hr) facts instructions
    50432 128 h50432 checked_50432
  have h50688 := Scan.chunk_sound (context_valid hr) facts instructions
    50560 128 h50560 checked_50560
  have h50816 := Scan.chunk_sound (context_valid hr) facts instructions
    50688 128 h50688 checked_50688
  have h50944 := Scan.chunk_sound (context_valid hr) facts instructions
    50816 128 h50816 checked_50816
  have h51072 := Scan.chunk_sound (context_valid hr) facts instructions
    50944 128 h50944 checked_50944
  have h51200 := Scan.chunk_sound (context_valid hr) facts instructions
    51072 128 h51072 checked_51072
  have h51328 := Scan.chunk_sound (context_valid hr) facts instructions
    51200 128 h51200 checked_51200
  have h51456 := Scan.chunk_sound (context_valid hr) facts instructions
    51328 128 h51328 checked_51328
  have h51584 := Scan.chunk_sound (context_valid hr) facts instructions
    51456 128 h51456 checked_51456
  have h51712 := Scan.chunk_sound (context_valid hr) facts instructions
    51584 128 h51584 checked_51584
  have h51840 := Scan.chunk_sound (context_valid hr) facts instructions
    51712 128 h51712 checked_51712
  have h51968 := Scan.chunk_sound (context_valid hr) facts instructions
    51840 128 h51840 checked_51840
  have h52096 := Scan.chunk_sound (context_valid hr) facts instructions
    51968 128 h51968 checked_51968
  have h52224 := Scan.chunk_sound (context_valid hr) facts instructions
    52096 128 h52096 checked_52096
  have h52352 := Scan.chunk_sound (context_valid hr) facts instructions
    52224 128 h52224 checked_52224
  have h52480 := Scan.chunk_sound (context_valid hr) facts instructions
    52352 128 h52352 checked_52352
  have h52608 := Scan.chunk_sound (context_valid hr) facts instructions
    52480 128 h52480 checked_52480
  have h52736 := Scan.chunk_sound (context_valid hr) facts instructions
    52608 128 h52608 checked_52608
  have h52864 := Scan.chunk_sound (context_valid hr) facts instructions
    52736 128 h52736 checked_52736
  have h52992 := Scan.chunk_sound (context_valid hr) facts instructions
    52864 128 h52864 checked_52864
  have h53120 := Scan.chunk_sound (context_valid hr) facts instructions
    52992 128 h52992 checked_52992
  have h53248 := Scan.chunk_sound (context_valid hr) facts instructions
    53120 128 h53120 checked_53120
  exact h53248

end Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced.Bound.LocalFinite.Certificate
