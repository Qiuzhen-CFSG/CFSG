module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.M1aBound.FiniteBound.Reduced.Bound.LocalFinite.Checks03

/-! Kernel checks for the conditional local coset certificate.
Each accepted step is an actual word deduction. The four relator identities
remain explicit premises; see `source/README.md`. -/

@[expose] public section
namespace Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced.Bound.LocalFinite.Certificate
open Subgroup.CosetWordCertificate

theorem checked_16384 : Scan.checkChunk context facts instructions 16384 128 = true := by
  decide +kernel

theorem checked_16512 : Scan.checkChunk context facts instructions 16512 128 = true := by
  decide +kernel

theorem checked_16640 : Scan.checkChunk context facts instructions 16640 128 = true := by
  decide +kernel

theorem checked_16768 : Scan.checkChunk context facts instructions 16768 128 = true := by
  decide +kernel

theorem checked_16896 : Scan.checkChunk context facts instructions 16896 128 = true := by
  decide +kernel

theorem checked_17024 : Scan.checkChunk context facts instructions 17024 128 = true := by
  decide +kernel

theorem checked_17152 : Scan.checkChunk context facts instructions 17152 128 = true := by
  decide +kernel

theorem checked_17280 : Scan.checkChunk context facts instructions 17280 128 = true := by
  decide +kernel

theorem checked_17408 : Scan.checkChunk context facts instructions 17408 128 = true := by
  decide +kernel

theorem checked_17536 : Scan.checkChunk context facts instructions 17536 128 = true := by
  decide +kernel

theorem checked_17664 : Scan.checkChunk context facts instructions 17664 128 = true := by
  decide +kernel

theorem checked_17792 : Scan.checkChunk context facts instructions 17792 128 = true := by
  decide +kernel

theorem checked_17920 : Scan.checkChunk context facts instructions 17920 128 = true := by
  decide +kernel

theorem checked_18048 : Scan.checkChunk context facts instructions 18048 128 = true := by
  decide +kernel

theorem checked_18176 : Scan.checkChunk context facts instructions 18176 128 = true := by
  decide +kernel

theorem checked_18304 : Scan.checkChunk context facts instructions 18304 128 = true := by
  decide +kernel

theorem checked_18432 : Scan.checkChunk context facts instructions 18432 128 = true := by
  decide +kernel

theorem checked_18560 : Scan.checkChunk context facts instructions 18560 128 = true := by
  decide +kernel

theorem checked_18688 : Scan.checkChunk context facts instructions 18688 128 = true := by
  decide +kernel

theorem checked_18816 : Scan.checkChunk context facts instructions 18816 128 = true := by
  decide +kernel

theorem checked_18944 : Scan.checkChunk context facts instructions 18944 128 = true := by
  decide +kernel

theorem checked_19072 : Scan.checkChunk context facts instructions 19072 128 = true := by
  decide +kernel

theorem checked_19200 : Scan.checkChunk context facts instructions 19200 128 = true := by
  decide +kernel

theorem checked_19328 : Scan.checkChunk context facts instructions 19328 128 = true := by
  decide +kernel

theorem checked_19456 : Scan.checkChunk context facts instructions 19456 128 = true := by
  decide +kernel

theorem checked_19584 : Scan.checkChunk context facts instructions 19584 128 = true := by
  decide +kernel

theorem checked_19712 : Scan.checkChunk context facts instructions 19712 128 = true := by
  decide +kernel

theorem checked_19840 : Scan.checkChunk context facts instructions 19840 128 = true := by
  decide +kernel

theorem checked_19968 : Scan.checkChunk context facts instructions 19968 128 = true := by
  decide +kernel

theorem checked_20096 : Scan.checkChunk context facts instructions 20096 128 = true := by
  decide +kernel

theorem checked_20224 : Scan.checkChunk context facts instructions 20224 128 = true := by
  decide +kernel

theorem checked_20352 : Scan.checkChunk context facts instructions 20352 128 = true := by
  decide +kernel

theorem holds_20480 (hr : ∀ r : Fin 4, eval subgroupGenerator (extraRelatorWord r) = 1) :
    ∀ n, n < 20480 → Holds smallSubgroup subgroupGenerator (definitions.repr subgroupGenerator) (facts n) := by
  have h16512 := Scan.chunk_sound (context_valid hr) facts instructions
    16384 128 (holds_16384 hr) checked_16384
  have h16640 := Scan.chunk_sound (context_valid hr) facts instructions
    16512 128 h16512 checked_16512
  have h16768 := Scan.chunk_sound (context_valid hr) facts instructions
    16640 128 h16640 checked_16640
  have h16896 := Scan.chunk_sound (context_valid hr) facts instructions
    16768 128 h16768 checked_16768
  have h17024 := Scan.chunk_sound (context_valid hr) facts instructions
    16896 128 h16896 checked_16896
  have h17152 := Scan.chunk_sound (context_valid hr) facts instructions
    17024 128 h17024 checked_17024
  have h17280 := Scan.chunk_sound (context_valid hr) facts instructions
    17152 128 h17152 checked_17152
  have h17408 := Scan.chunk_sound (context_valid hr) facts instructions
    17280 128 h17280 checked_17280
  have h17536 := Scan.chunk_sound (context_valid hr) facts instructions
    17408 128 h17408 checked_17408
  have h17664 := Scan.chunk_sound (context_valid hr) facts instructions
    17536 128 h17536 checked_17536
  have h17792 := Scan.chunk_sound (context_valid hr) facts instructions
    17664 128 h17664 checked_17664
  have h17920 := Scan.chunk_sound (context_valid hr) facts instructions
    17792 128 h17792 checked_17792
  have h18048 := Scan.chunk_sound (context_valid hr) facts instructions
    17920 128 h17920 checked_17920
  have h18176 := Scan.chunk_sound (context_valid hr) facts instructions
    18048 128 h18048 checked_18048
  have h18304 := Scan.chunk_sound (context_valid hr) facts instructions
    18176 128 h18176 checked_18176
  have h18432 := Scan.chunk_sound (context_valid hr) facts instructions
    18304 128 h18304 checked_18304
  have h18560 := Scan.chunk_sound (context_valid hr) facts instructions
    18432 128 h18432 checked_18432
  have h18688 := Scan.chunk_sound (context_valid hr) facts instructions
    18560 128 h18560 checked_18560
  have h18816 := Scan.chunk_sound (context_valid hr) facts instructions
    18688 128 h18688 checked_18688
  have h18944 := Scan.chunk_sound (context_valid hr) facts instructions
    18816 128 h18816 checked_18816
  have h19072 := Scan.chunk_sound (context_valid hr) facts instructions
    18944 128 h18944 checked_18944
  have h19200 := Scan.chunk_sound (context_valid hr) facts instructions
    19072 128 h19072 checked_19072
  have h19328 := Scan.chunk_sound (context_valid hr) facts instructions
    19200 128 h19200 checked_19200
  have h19456 := Scan.chunk_sound (context_valid hr) facts instructions
    19328 128 h19328 checked_19328
  have h19584 := Scan.chunk_sound (context_valid hr) facts instructions
    19456 128 h19456 checked_19456
  have h19712 := Scan.chunk_sound (context_valid hr) facts instructions
    19584 128 h19584 checked_19584
  have h19840 := Scan.chunk_sound (context_valid hr) facts instructions
    19712 128 h19712 checked_19712
  have h19968 := Scan.chunk_sound (context_valid hr) facts instructions
    19840 128 h19840 checked_19840
  have h20096 := Scan.chunk_sound (context_valid hr) facts instructions
    19968 128 h19968 checked_19968
  have h20224 := Scan.chunk_sound (context_valid hr) facts instructions
    20096 128 h20096 checked_20096
  have h20352 := Scan.chunk_sound (context_valid hr) facts instructions
    20224 128 h20224 checked_20224
  have h20480 := Scan.chunk_sound (context_valid hr) facts instructions
    20352 128 h20352 checked_20352
  exact h20480

end Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced.Bound.LocalFinite.Certificate
