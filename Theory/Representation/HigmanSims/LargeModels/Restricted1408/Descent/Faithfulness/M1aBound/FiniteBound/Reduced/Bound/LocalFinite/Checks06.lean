module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.M1aBound.FiniteBound.Reduced.Bound.LocalFinite.Checks05

/-! Kernel checks for the conditional local coset certificate.
Each accepted step is an actual word deduction. The four relator identities
remain explicit premises; see `source/README.md`. -/

@[expose] public section
namespace Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced.Bound.LocalFinite.Certificate
open Subgroup.CosetWordCertificate

theorem checked_24576 : Scan.checkChunk context facts instructions 24576 128 = true := by
  decide +kernel

theorem checked_24704 : Scan.checkChunk context facts instructions 24704 128 = true := by
  decide +kernel

theorem checked_24832 : Scan.checkChunk context facts instructions 24832 128 = true := by
  decide +kernel

theorem checked_24960 : Scan.checkChunk context facts instructions 24960 128 = true := by
  decide +kernel

theorem checked_25088 : Scan.checkChunk context facts instructions 25088 128 = true := by
  decide +kernel

theorem checked_25216 : Scan.checkChunk context facts instructions 25216 128 = true := by
  decide +kernel

theorem checked_25344 : Scan.checkChunk context facts instructions 25344 128 = true := by
  decide +kernel

theorem checked_25472 : Scan.checkChunk context facts instructions 25472 128 = true := by
  decide +kernel

theorem checked_25600 : Scan.checkChunk context facts instructions 25600 128 = true := by
  decide +kernel

theorem checked_25728 : Scan.checkChunk context facts instructions 25728 128 = true := by
  decide +kernel

theorem checked_25856 : Scan.checkChunk context facts instructions 25856 128 = true := by
  decide +kernel

theorem checked_25984 : Scan.checkChunk context facts instructions 25984 128 = true := by
  decide +kernel

theorem checked_26112 : Scan.checkChunk context facts instructions 26112 128 = true := by
  decide +kernel

theorem checked_26240 : Scan.checkChunk context facts instructions 26240 128 = true := by
  decide +kernel

theorem checked_26368 : Scan.checkChunk context facts instructions 26368 128 = true := by
  decide +kernel

theorem checked_26496 : Scan.checkChunk context facts instructions 26496 128 = true := by
  decide +kernel

theorem checked_26624 : Scan.checkChunk context facts instructions 26624 128 = true := by
  decide +kernel

theorem checked_26752 : Scan.checkChunk context facts instructions 26752 128 = true := by
  decide +kernel

theorem checked_26880 : Scan.checkChunk context facts instructions 26880 128 = true := by
  decide +kernel

theorem checked_27008 : Scan.checkChunk context facts instructions 27008 128 = true := by
  decide +kernel

theorem checked_27136 : Scan.checkChunk context facts instructions 27136 128 = true := by
  decide +kernel

theorem checked_27264 : Scan.checkChunk context facts instructions 27264 128 = true := by
  decide +kernel

theorem checked_27392 : Scan.checkChunk context facts instructions 27392 128 = true := by
  decide +kernel

theorem checked_27520 : Scan.checkChunk context facts instructions 27520 128 = true := by
  decide +kernel

theorem checked_27648 : Scan.checkChunk context facts instructions 27648 128 = true := by
  decide +kernel

theorem checked_27776 : Scan.checkChunk context facts instructions 27776 128 = true := by
  decide +kernel

theorem checked_27904 : Scan.checkChunk context facts instructions 27904 128 = true := by
  decide +kernel

theorem checked_28032 : Scan.checkChunk context facts instructions 28032 128 = true := by
  decide +kernel

theorem checked_28160 : Scan.checkChunk context facts instructions 28160 128 = true := by
  decide +kernel

theorem checked_28288 : Scan.checkChunk context facts instructions 28288 128 = true := by
  decide +kernel

theorem checked_28416 : Scan.checkChunk context facts instructions 28416 128 = true := by
  decide +kernel

theorem checked_28544 : Scan.checkChunk context facts instructions 28544 128 = true := by
  decide +kernel

theorem holds_28672 (hr : ∀ r : Fin 4, eval subgroupGenerator (extraRelatorWord r) = 1) :
    ∀ n, n < 28672 → Holds smallSubgroup subgroupGenerator (definitions.repr subgroupGenerator) (facts n) := by
  have h24704 := Scan.chunk_sound (context_valid hr) facts instructions
    24576 128 (holds_24576 hr) checked_24576
  have h24832 := Scan.chunk_sound (context_valid hr) facts instructions
    24704 128 h24704 checked_24704
  have h24960 := Scan.chunk_sound (context_valid hr) facts instructions
    24832 128 h24832 checked_24832
  have h25088 := Scan.chunk_sound (context_valid hr) facts instructions
    24960 128 h24960 checked_24960
  have h25216 := Scan.chunk_sound (context_valid hr) facts instructions
    25088 128 h25088 checked_25088
  have h25344 := Scan.chunk_sound (context_valid hr) facts instructions
    25216 128 h25216 checked_25216
  have h25472 := Scan.chunk_sound (context_valid hr) facts instructions
    25344 128 h25344 checked_25344
  have h25600 := Scan.chunk_sound (context_valid hr) facts instructions
    25472 128 h25472 checked_25472
  have h25728 := Scan.chunk_sound (context_valid hr) facts instructions
    25600 128 h25600 checked_25600
  have h25856 := Scan.chunk_sound (context_valid hr) facts instructions
    25728 128 h25728 checked_25728
  have h25984 := Scan.chunk_sound (context_valid hr) facts instructions
    25856 128 h25856 checked_25856
  have h26112 := Scan.chunk_sound (context_valid hr) facts instructions
    25984 128 h25984 checked_25984
  have h26240 := Scan.chunk_sound (context_valid hr) facts instructions
    26112 128 h26112 checked_26112
  have h26368 := Scan.chunk_sound (context_valid hr) facts instructions
    26240 128 h26240 checked_26240
  have h26496 := Scan.chunk_sound (context_valid hr) facts instructions
    26368 128 h26368 checked_26368
  have h26624 := Scan.chunk_sound (context_valid hr) facts instructions
    26496 128 h26496 checked_26496
  have h26752 := Scan.chunk_sound (context_valid hr) facts instructions
    26624 128 h26624 checked_26624
  have h26880 := Scan.chunk_sound (context_valid hr) facts instructions
    26752 128 h26752 checked_26752
  have h27008 := Scan.chunk_sound (context_valid hr) facts instructions
    26880 128 h26880 checked_26880
  have h27136 := Scan.chunk_sound (context_valid hr) facts instructions
    27008 128 h27008 checked_27008
  have h27264 := Scan.chunk_sound (context_valid hr) facts instructions
    27136 128 h27136 checked_27136
  have h27392 := Scan.chunk_sound (context_valid hr) facts instructions
    27264 128 h27264 checked_27264
  have h27520 := Scan.chunk_sound (context_valid hr) facts instructions
    27392 128 h27392 checked_27392
  have h27648 := Scan.chunk_sound (context_valid hr) facts instructions
    27520 128 h27520 checked_27520
  have h27776 := Scan.chunk_sound (context_valid hr) facts instructions
    27648 128 h27648 checked_27648
  have h27904 := Scan.chunk_sound (context_valid hr) facts instructions
    27776 128 h27776 checked_27776
  have h28032 := Scan.chunk_sound (context_valid hr) facts instructions
    27904 128 h27904 checked_27904
  have h28160 := Scan.chunk_sound (context_valid hr) facts instructions
    28032 128 h28032 checked_28032
  have h28288 := Scan.chunk_sound (context_valid hr) facts instructions
    28160 128 h28160 checked_28160
  have h28416 := Scan.chunk_sound (context_valid hr) facts instructions
    28288 128 h28288 checked_28288
  have h28544 := Scan.chunk_sound (context_valid hr) facts instructions
    28416 128 h28416 checked_28416
  have h28672 := Scan.chunk_sound (context_valid hr) facts instructions
    28544 128 h28544 checked_28544
  exact h28672

end Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced.Bound.LocalFinite.Certificate
