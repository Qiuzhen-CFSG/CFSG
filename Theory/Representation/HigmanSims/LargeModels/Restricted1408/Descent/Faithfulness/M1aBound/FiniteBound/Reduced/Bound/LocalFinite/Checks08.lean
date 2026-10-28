module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.M1aBound.FiniteBound.Reduced.Bound.LocalFinite.Checks07

/-! Kernel checks for the conditional local coset certificate.
Each accepted step is an actual word deduction. The four relator identities
remain explicit premises; see `source/README.md`. -/

@[expose] public section
namespace Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced.Bound.LocalFinite.Certificate
open Subgroup.CosetWordCertificate

theorem checked_32768 : Scan.checkChunk context facts instructions 32768 128 = true := by
  decide +kernel

theorem checked_32896 : Scan.checkChunk context facts instructions 32896 128 = true := by
  decide +kernel

theorem checked_33024 : Scan.checkChunk context facts instructions 33024 128 = true := by
  decide +kernel

theorem checked_33152 : Scan.checkChunk context facts instructions 33152 128 = true := by
  decide +kernel

theorem checked_33280 : Scan.checkChunk context facts instructions 33280 128 = true := by
  decide +kernel

theorem checked_33408 : Scan.checkChunk context facts instructions 33408 128 = true := by
  decide +kernel

theorem checked_33536 : Scan.checkChunk context facts instructions 33536 128 = true := by
  decide +kernel

theorem checked_33664 : Scan.checkChunk context facts instructions 33664 128 = true := by
  decide +kernel

theorem checked_33792 : Scan.checkChunk context facts instructions 33792 128 = true := by
  decide +kernel

theorem checked_33920 : Scan.checkChunk context facts instructions 33920 128 = true := by
  decide +kernel

theorem checked_34048 : Scan.checkChunk context facts instructions 34048 128 = true := by
  decide +kernel

theorem checked_34176 : Scan.checkChunk context facts instructions 34176 128 = true := by
  decide +kernel

theorem checked_34304 : Scan.checkChunk context facts instructions 34304 128 = true := by
  decide +kernel

theorem checked_34432 : Scan.checkChunk context facts instructions 34432 128 = true := by
  decide +kernel

theorem checked_34560 : Scan.checkChunk context facts instructions 34560 128 = true := by
  decide +kernel

theorem checked_34688 : Scan.checkChunk context facts instructions 34688 128 = true := by
  decide +kernel

theorem checked_34816 : Scan.checkChunk context facts instructions 34816 128 = true := by
  decide +kernel

theorem checked_34944 : Scan.checkChunk context facts instructions 34944 128 = true := by
  decide +kernel

theorem checked_35072 : Scan.checkChunk context facts instructions 35072 128 = true := by
  decide +kernel

theorem checked_35200 : Scan.checkChunk context facts instructions 35200 128 = true := by
  decide +kernel

theorem checked_35328 : Scan.checkChunk context facts instructions 35328 128 = true := by
  decide +kernel

theorem checked_35456 : Scan.checkChunk context facts instructions 35456 128 = true := by
  decide +kernel

theorem checked_35584 : Scan.checkChunk context facts instructions 35584 128 = true := by
  decide +kernel

theorem checked_35712 : Scan.checkChunk context facts instructions 35712 128 = true := by
  decide +kernel

theorem checked_35840 : Scan.checkChunk context facts instructions 35840 128 = true := by
  decide +kernel

theorem checked_35968 : Scan.checkChunk context facts instructions 35968 128 = true := by
  decide +kernel

theorem checked_36096 : Scan.checkChunk context facts instructions 36096 128 = true := by
  decide +kernel

theorem checked_36224 : Scan.checkChunk context facts instructions 36224 128 = true := by
  decide +kernel

theorem checked_36352 : Scan.checkChunk context facts instructions 36352 128 = true := by
  decide +kernel

theorem checked_36480 : Scan.checkChunk context facts instructions 36480 128 = true := by
  decide +kernel

theorem checked_36608 : Scan.checkChunk context facts instructions 36608 128 = true := by
  decide +kernel

theorem checked_36736 : Scan.checkChunk context facts instructions 36736 128 = true := by
  decide +kernel

theorem holds_36864 (hr : ∀ r : Fin 4, eval subgroupGenerator (extraRelatorWord r) = 1) :
    ∀ n, n < 36864 → Holds smallSubgroup subgroupGenerator (definitions.repr subgroupGenerator) (facts n) := by
  have h32896 := Scan.chunk_sound (context_valid hr) facts instructions
    32768 128 (holds_32768 hr) checked_32768
  have h33024 := Scan.chunk_sound (context_valid hr) facts instructions
    32896 128 h32896 checked_32896
  have h33152 := Scan.chunk_sound (context_valid hr) facts instructions
    33024 128 h33024 checked_33024
  have h33280 := Scan.chunk_sound (context_valid hr) facts instructions
    33152 128 h33152 checked_33152
  have h33408 := Scan.chunk_sound (context_valid hr) facts instructions
    33280 128 h33280 checked_33280
  have h33536 := Scan.chunk_sound (context_valid hr) facts instructions
    33408 128 h33408 checked_33408
  have h33664 := Scan.chunk_sound (context_valid hr) facts instructions
    33536 128 h33536 checked_33536
  have h33792 := Scan.chunk_sound (context_valid hr) facts instructions
    33664 128 h33664 checked_33664
  have h33920 := Scan.chunk_sound (context_valid hr) facts instructions
    33792 128 h33792 checked_33792
  have h34048 := Scan.chunk_sound (context_valid hr) facts instructions
    33920 128 h33920 checked_33920
  have h34176 := Scan.chunk_sound (context_valid hr) facts instructions
    34048 128 h34048 checked_34048
  have h34304 := Scan.chunk_sound (context_valid hr) facts instructions
    34176 128 h34176 checked_34176
  have h34432 := Scan.chunk_sound (context_valid hr) facts instructions
    34304 128 h34304 checked_34304
  have h34560 := Scan.chunk_sound (context_valid hr) facts instructions
    34432 128 h34432 checked_34432
  have h34688 := Scan.chunk_sound (context_valid hr) facts instructions
    34560 128 h34560 checked_34560
  have h34816 := Scan.chunk_sound (context_valid hr) facts instructions
    34688 128 h34688 checked_34688
  have h34944 := Scan.chunk_sound (context_valid hr) facts instructions
    34816 128 h34816 checked_34816
  have h35072 := Scan.chunk_sound (context_valid hr) facts instructions
    34944 128 h34944 checked_34944
  have h35200 := Scan.chunk_sound (context_valid hr) facts instructions
    35072 128 h35072 checked_35072
  have h35328 := Scan.chunk_sound (context_valid hr) facts instructions
    35200 128 h35200 checked_35200
  have h35456 := Scan.chunk_sound (context_valid hr) facts instructions
    35328 128 h35328 checked_35328
  have h35584 := Scan.chunk_sound (context_valid hr) facts instructions
    35456 128 h35456 checked_35456
  have h35712 := Scan.chunk_sound (context_valid hr) facts instructions
    35584 128 h35584 checked_35584
  have h35840 := Scan.chunk_sound (context_valid hr) facts instructions
    35712 128 h35712 checked_35712
  have h35968 := Scan.chunk_sound (context_valid hr) facts instructions
    35840 128 h35840 checked_35840
  have h36096 := Scan.chunk_sound (context_valid hr) facts instructions
    35968 128 h35968 checked_35968
  have h36224 := Scan.chunk_sound (context_valid hr) facts instructions
    36096 128 h36096 checked_36096
  have h36352 := Scan.chunk_sound (context_valid hr) facts instructions
    36224 128 h36224 checked_36224
  have h36480 := Scan.chunk_sound (context_valid hr) facts instructions
    36352 128 h36352 checked_36352
  have h36608 := Scan.chunk_sound (context_valid hr) facts instructions
    36480 128 h36480 checked_36480
  have h36736 := Scan.chunk_sound (context_valid hr) facts instructions
    36608 128 h36608 checked_36608
  have h36864 := Scan.chunk_sound (context_valid hr) facts instructions
    36736 128 h36736 checked_36736
  exact h36864

end Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced.Bound.LocalFinite.Certificate
