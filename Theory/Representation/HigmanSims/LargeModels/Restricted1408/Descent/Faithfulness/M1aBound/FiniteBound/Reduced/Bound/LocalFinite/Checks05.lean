module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.M1aBound.FiniteBound.Reduced.Bound.LocalFinite.Checks04

/-! Kernel checks for the conditional local coset certificate.
Each accepted step is an actual word deduction. The four relator identities
remain explicit premises; see `source/README.md`. -/

@[expose] public section
namespace Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced.Bound.LocalFinite.Certificate
open Subgroup.CosetWordCertificate

theorem checked_20480 : Scan.checkChunk context facts instructions 20480 128 = true := by
  decide +kernel

theorem checked_20608 : Scan.checkChunk context facts instructions 20608 128 = true := by
  decide +kernel

theorem checked_20736 : Scan.checkChunk context facts instructions 20736 128 = true := by
  decide +kernel

theorem checked_20864 : Scan.checkChunk context facts instructions 20864 128 = true := by
  decide +kernel

theorem checked_20992 : Scan.checkChunk context facts instructions 20992 128 = true := by
  decide +kernel

theorem checked_21120 : Scan.checkChunk context facts instructions 21120 128 = true := by
  decide +kernel

theorem checked_21248 : Scan.checkChunk context facts instructions 21248 128 = true := by
  decide +kernel

theorem checked_21376 : Scan.checkChunk context facts instructions 21376 128 = true := by
  decide +kernel

theorem checked_21504 : Scan.checkChunk context facts instructions 21504 128 = true := by
  decide +kernel

theorem checked_21632 : Scan.checkChunk context facts instructions 21632 128 = true := by
  decide +kernel

theorem checked_21760 : Scan.checkChunk context facts instructions 21760 128 = true := by
  decide +kernel

theorem checked_21888 : Scan.checkChunk context facts instructions 21888 128 = true := by
  decide +kernel

theorem checked_22016 : Scan.checkChunk context facts instructions 22016 128 = true := by
  decide +kernel

theorem checked_22144 : Scan.checkChunk context facts instructions 22144 128 = true := by
  decide +kernel

theorem checked_22272 : Scan.checkChunk context facts instructions 22272 128 = true := by
  decide +kernel

theorem checked_22400 : Scan.checkChunk context facts instructions 22400 128 = true := by
  decide +kernel

theorem checked_22528 : Scan.checkChunk context facts instructions 22528 128 = true := by
  decide +kernel

theorem checked_22656 : Scan.checkChunk context facts instructions 22656 128 = true := by
  decide +kernel

theorem checked_22784 : Scan.checkChunk context facts instructions 22784 128 = true := by
  decide +kernel

theorem checked_22912 : Scan.checkChunk context facts instructions 22912 128 = true := by
  decide +kernel

theorem checked_23040 : Scan.checkChunk context facts instructions 23040 128 = true := by
  decide +kernel

theorem checked_23168 : Scan.checkChunk context facts instructions 23168 128 = true := by
  decide +kernel

theorem checked_23296 : Scan.checkChunk context facts instructions 23296 128 = true := by
  decide +kernel

theorem checked_23424 : Scan.checkChunk context facts instructions 23424 128 = true := by
  decide +kernel

theorem checked_23552 : Scan.checkChunk context facts instructions 23552 128 = true := by
  decide +kernel

theorem checked_23680 : Scan.checkChunk context facts instructions 23680 128 = true := by
  decide +kernel

theorem checked_23808 : Scan.checkChunk context facts instructions 23808 128 = true := by
  decide +kernel

theorem checked_23936 : Scan.checkChunk context facts instructions 23936 128 = true := by
  decide +kernel

theorem checked_24064 : Scan.checkChunk context facts instructions 24064 128 = true := by
  decide +kernel

theorem checked_24192 : Scan.checkChunk context facts instructions 24192 128 = true := by
  decide +kernel

theorem checked_24320 : Scan.checkChunk context facts instructions 24320 128 = true := by
  decide +kernel

theorem checked_24448 : Scan.checkChunk context facts instructions 24448 128 = true := by
  decide +kernel

theorem holds_24576 (hr : ∀ r : Fin 4, eval subgroupGenerator (extraRelatorWord r) = 1) :
    ∀ n, n < 24576 → Holds smallSubgroup subgroupGenerator (definitions.repr subgroupGenerator) (facts n) := by
  have h20608 := Scan.chunk_sound (context_valid hr) facts instructions
    20480 128 (holds_20480 hr) checked_20480
  have h20736 := Scan.chunk_sound (context_valid hr) facts instructions
    20608 128 h20608 checked_20608
  have h20864 := Scan.chunk_sound (context_valid hr) facts instructions
    20736 128 h20736 checked_20736
  have h20992 := Scan.chunk_sound (context_valid hr) facts instructions
    20864 128 h20864 checked_20864
  have h21120 := Scan.chunk_sound (context_valid hr) facts instructions
    20992 128 h20992 checked_20992
  have h21248 := Scan.chunk_sound (context_valid hr) facts instructions
    21120 128 h21120 checked_21120
  have h21376 := Scan.chunk_sound (context_valid hr) facts instructions
    21248 128 h21248 checked_21248
  have h21504 := Scan.chunk_sound (context_valid hr) facts instructions
    21376 128 h21376 checked_21376
  have h21632 := Scan.chunk_sound (context_valid hr) facts instructions
    21504 128 h21504 checked_21504
  have h21760 := Scan.chunk_sound (context_valid hr) facts instructions
    21632 128 h21632 checked_21632
  have h21888 := Scan.chunk_sound (context_valid hr) facts instructions
    21760 128 h21760 checked_21760
  have h22016 := Scan.chunk_sound (context_valid hr) facts instructions
    21888 128 h21888 checked_21888
  have h22144 := Scan.chunk_sound (context_valid hr) facts instructions
    22016 128 h22016 checked_22016
  have h22272 := Scan.chunk_sound (context_valid hr) facts instructions
    22144 128 h22144 checked_22144
  have h22400 := Scan.chunk_sound (context_valid hr) facts instructions
    22272 128 h22272 checked_22272
  have h22528 := Scan.chunk_sound (context_valid hr) facts instructions
    22400 128 h22400 checked_22400
  have h22656 := Scan.chunk_sound (context_valid hr) facts instructions
    22528 128 h22528 checked_22528
  have h22784 := Scan.chunk_sound (context_valid hr) facts instructions
    22656 128 h22656 checked_22656
  have h22912 := Scan.chunk_sound (context_valid hr) facts instructions
    22784 128 h22784 checked_22784
  have h23040 := Scan.chunk_sound (context_valid hr) facts instructions
    22912 128 h22912 checked_22912
  have h23168 := Scan.chunk_sound (context_valid hr) facts instructions
    23040 128 h23040 checked_23040
  have h23296 := Scan.chunk_sound (context_valid hr) facts instructions
    23168 128 h23168 checked_23168
  have h23424 := Scan.chunk_sound (context_valid hr) facts instructions
    23296 128 h23296 checked_23296
  have h23552 := Scan.chunk_sound (context_valid hr) facts instructions
    23424 128 h23424 checked_23424
  have h23680 := Scan.chunk_sound (context_valid hr) facts instructions
    23552 128 h23552 checked_23552
  have h23808 := Scan.chunk_sound (context_valid hr) facts instructions
    23680 128 h23680 checked_23680
  have h23936 := Scan.chunk_sound (context_valid hr) facts instructions
    23808 128 h23808 checked_23808
  have h24064 := Scan.chunk_sound (context_valid hr) facts instructions
    23936 128 h23936 checked_23936
  have h24192 := Scan.chunk_sound (context_valid hr) facts instructions
    24064 128 h24064 checked_24064
  have h24320 := Scan.chunk_sound (context_valid hr) facts instructions
    24192 128 h24192 checked_24192
  have h24448 := Scan.chunk_sound (context_valid hr) facts instructions
    24320 128 h24320 checked_24320
  have h24576 := Scan.chunk_sound (context_valid hr) facts instructions
    24448 128 h24448 checked_24448
  exact h24576

end Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced.Bound.LocalFinite.Certificate
