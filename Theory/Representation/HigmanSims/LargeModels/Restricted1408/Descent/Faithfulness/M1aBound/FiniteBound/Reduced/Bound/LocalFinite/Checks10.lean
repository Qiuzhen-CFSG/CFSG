module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.M1aBound.FiniteBound.Reduced.Bound.LocalFinite.Checks09

/-! Kernel checks for the conditional local coset certificate.
Each accepted step is an actual word deduction. The four relator identities
remain explicit premises; see `source/README.md`. -/

@[expose] public section
namespace Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced.Bound.LocalFinite.Certificate
open Subgroup.CosetWordCertificate

theorem checked_40960 : Scan.checkChunk context facts instructions 40960 128 = true := by
  decide +kernel

theorem checked_41088 : Scan.checkChunk context facts instructions 41088 128 = true := by
  decide +kernel

theorem checked_41216 : Scan.checkChunk context facts instructions 41216 128 = true := by
  decide +kernel

theorem checked_41344 : Scan.checkChunk context facts instructions 41344 128 = true := by
  decide +kernel

theorem checked_41472 : Scan.checkChunk context facts instructions 41472 128 = true := by
  decide +kernel

theorem checked_41600 : Scan.checkChunk context facts instructions 41600 128 = true := by
  decide +kernel

theorem checked_41728 : Scan.checkChunk context facts instructions 41728 128 = true := by
  decide +kernel

theorem checked_41856 : Scan.checkChunk context facts instructions 41856 128 = true := by
  decide +kernel

theorem checked_41984 : Scan.checkChunk context facts instructions 41984 128 = true := by
  decide +kernel

theorem checked_42112 : Scan.checkChunk context facts instructions 42112 128 = true := by
  decide +kernel

theorem checked_42240 : Scan.checkChunk context facts instructions 42240 128 = true := by
  decide +kernel

theorem checked_42368 : Scan.checkChunk context facts instructions 42368 128 = true := by
  decide +kernel

theorem checked_42496 : Scan.checkChunk context facts instructions 42496 128 = true := by
  decide +kernel

theorem checked_42624 : Scan.checkChunk context facts instructions 42624 128 = true := by
  decide +kernel

theorem checked_42752 : Scan.checkChunk context facts instructions 42752 128 = true := by
  decide +kernel

theorem checked_42880 : Scan.checkChunk context facts instructions 42880 128 = true := by
  decide +kernel

theorem checked_43008 : Scan.checkChunk context facts instructions 43008 128 = true := by
  decide +kernel

theorem checked_43136 : Scan.checkChunk context facts instructions 43136 128 = true := by
  decide +kernel

theorem checked_43264 : Scan.checkChunk context facts instructions 43264 128 = true := by
  decide +kernel

theorem checked_43392 : Scan.checkChunk context facts instructions 43392 128 = true := by
  decide +kernel

theorem checked_43520 : Scan.checkChunk context facts instructions 43520 128 = true := by
  decide +kernel

theorem checked_43648 : Scan.checkChunk context facts instructions 43648 128 = true := by
  decide +kernel

theorem checked_43776 : Scan.checkChunk context facts instructions 43776 128 = true := by
  decide +kernel

theorem checked_43904 : Scan.checkChunk context facts instructions 43904 128 = true := by
  decide +kernel

theorem checked_44032 : Scan.checkChunk context facts instructions 44032 128 = true := by
  decide +kernel

theorem checked_44160 : Scan.checkChunk context facts instructions 44160 128 = true := by
  decide +kernel

theorem checked_44288 : Scan.checkChunk context facts instructions 44288 128 = true := by
  decide +kernel

theorem checked_44416 : Scan.checkChunk context facts instructions 44416 128 = true := by
  decide +kernel

theorem checked_44544 : Scan.checkChunk context facts instructions 44544 128 = true := by
  decide +kernel

theorem checked_44672 : Scan.checkChunk context facts instructions 44672 128 = true := by
  decide +kernel

theorem checked_44800 : Scan.checkChunk context facts instructions 44800 128 = true := by
  decide +kernel

theorem checked_44928 : Scan.checkChunk context facts instructions 44928 128 = true := by
  decide +kernel

theorem holds_45056 (hr : ∀ r : Fin 4, eval subgroupGenerator (extraRelatorWord r) = 1) :
    ∀ n, n < 45056 → Holds smallSubgroup subgroupGenerator (definitions.repr subgroupGenerator) (facts n) := by
  have h41088 := Scan.chunk_sound (context_valid hr) facts instructions
    40960 128 (holds_40960 hr) checked_40960
  have h41216 := Scan.chunk_sound (context_valid hr) facts instructions
    41088 128 h41088 checked_41088
  have h41344 := Scan.chunk_sound (context_valid hr) facts instructions
    41216 128 h41216 checked_41216
  have h41472 := Scan.chunk_sound (context_valid hr) facts instructions
    41344 128 h41344 checked_41344
  have h41600 := Scan.chunk_sound (context_valid hr) facts instructions
    41472 128 h41472 checked_41472
  have h41728 := Scan.chunk_sound (context_valid hr) facts instructions
    41600 128 h41600 checked_41600
  have h41856 := Scan.chunk_sound (context_valid hr) facts instructions
    41728 128 h41728 checked_41728
  have h41984 := Scan.chunk_sound (context_valid hr) facts instructions
    41856 128 h41856 checked_41856
  have h42112 := Scan.chunk_sound (context_valid hr) facts instructions
    41984 128 h41984 checked_41984
  have h42240 := Scan.chunk_sound (context_valid hr) facts instructions
    42112 128 h42112 checked_42112
  have h42368 := Scan.chunk_sound (context_valid hr) facts instructions
    42240 128 h42240 checked_42240
  have h42496 := Scan.chunk_sound (context_valid hr) facts instructions
    42368 128 h42368 checked_42368
  have h42624 := Scan.chunk_sound (context_valid hr) facts instructions
    42496 128 h42496 checked_42496
  have h42752 := Scan.chunk_sound (context_valid hr) facts instructions
    42624 128 h42624 checked_42624
  have h42880 := Scan.chunk_sound (context_valid hr) facts instructions
    42752 128 h42752 checked_42752
  have h43008 := Scan.chunk_sound (context_valid hr) facts instructions
    42880 128 h42880 checked_42880
  have h43136 := Scan.chunk_sound (context_valid hr) facts instructions
    43008 128 h43008 checked_43008
  have h43264 := Scan.chunk_sound (context_valid hr) facts instructions
    43136 128 h43136 checked_43136
  have h43392 := Scan.chunk_sound (context_valid hr) facts instructions
    43264 128 h43264 checked_43264
  have h43520 := Scan.chunk_sound (context_valid hr) facts instructions
    43392 128 h43392 checked_43392
  have h43648 := Scan.chunk_sound (context_valid hr) facts instructions
    43520 128 h43520 checked_43520
  have h43776 := Scan.chunk_sound (context_valid hr) facts instructions
    43648 128 h43648 checked_43648
  have h43904 := Scan.chunk_sound (context_valid hr) facts instructions
    43776 128 h43776 checked_43776
  have h44032 := Scan.chunk_sound (context_valid hr) facts instructions
    43904 128 h43904 checked_43904
  have h44160 := Scan.chunk_sound (context_valid hr) facts instructions
    44032 128 h44032 checked_44032
  have h44288 := Scan.chunk_sound (context_valid hr) facts instructions
    44160 128 h44160 checked_44160
  have h44416 := Scan.chunk_sound (context_valid hr) facts instructions
    44288 128 h44288 checked_44288
  have h44544 := Scan.chunk_sound (context_valid hr) facts instructions
    44416 128 h44416 checked_44416
  have h44672 := Scan.chunk_sound (context_valid hr) facts instructions
    44544 128 h44544 checked_44544
  have h44800 := Scan.chunk_sound (context_valid hr) facts instructions
    44672 128 h44672 checked_44672
  have h44928 := Scan.chunk_sound (context_valid hr) facts instructions
    44800 128 h44800 checked_44800
  have h45056 := Scan.chunk_sound (context_valid hr) facts instructions
    44928 128 h44928 checked_44928
  exact h45056

end Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced.Bound.LocalFinite.Certificate
