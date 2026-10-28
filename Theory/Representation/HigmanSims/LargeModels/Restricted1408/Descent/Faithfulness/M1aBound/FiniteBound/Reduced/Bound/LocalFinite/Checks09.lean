module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.M1aBound.FiniteBound.Reduced.Bound.LocalFinite.Checks08

/-! Kernel checks for the conditional local coset certificate.
Each accepted step is an actual word deduction. The four relator identities
remain explicit premises; see `source/README.md`. -/

@[expose] public section
namespace Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced.Bound.LocalFinite.Certificate
open Subgroup.CosetWordCertificate

theorem checked_36864 : Scan.checkChunk context facts instructions 36864 128 = true := by
  decide +kernel

theorem checked_36992 : Scan.checkChunk context facts instructions 36992 128 = true := by
  decide +kernel

theorem checked_37120 : Scan.checkChunk context facts instructions 37120 128 = true := by
  decide +kernel

theorem checked_37248 : Scan.checkChunk context facts instructions 37248 128 = true := by
  decide +kernel

theorem checked_37376 : Scan.checkChunk context facts instructions 37376 128 = true := by
  decide +kernel

theorem checked_37504 : Scan.checkChunk context facts instructions 37504 128 = true := by
  decide +kernel

theorem checked_37632 : Scan.checkChunk context facts instructions 37632 128 = true := by
  decide +kernel

theorem checked_37760 : Scan.checkChunk context facts instructions 37760 128 = true := by
  decide +kernel

theorem checked_37888 : Scan.checkChunk context facts instructions 37888 128 = true := by
  decide +kernel

theorem checked_38016 : Scan.checkChunk context facts instructions 38016 128 = true := by
  decide +kernel

theorem checked_38144 : Scan.checkChunk context facts instructions 38144 128 = true := by
  decide +kernel

theorem checked_38272 : Scan.checkChunk context facts instructions 38272 128 = true := by
  decide +kernel

theorem checked_38400 : Scan.checkChunk context facts instructions 38400 128 = true := by
  decide +kernel

theorem checked_38528 : Scan.checkChunk context facts instructions 38528 128 = true := by
  decide +kernel

theorem checked_38656 : Scan.checkChunk context facts instructions 38656 128 = true := by
  decide +kernel

theorem checked_38784 : Scan.checkChunk context facts instructions 38784 128 = true := by
  decide +kernel

theorem checked_38912 : Scan.checkChunk context facts instructions 38912 128 = true := by
  decide +kernel

theorem checked_39040 : Scan.checkChunk context facts instructions 39040 128 = true := by
  decide +kernel

theorem checked_39168 : Scan.checkChunk context facts instructions 39168 128 = true := by
  decide +kernel

theorem checked_39296 : Scan.checkChunk context facts instructions 39296 128 = true := by
  decide +kernel

theorem checked_39424 : Scan.checkChunk context facts instructions 39424 128 = true := by
  decide +kernel

theorem checked_39552 : Scan.checkChunk context facts instructions 39552 128 = true := by
  decide +kernel

theorem checked_39680 : Scan.checkChunk context facts instructions 39680 128 = true := by
  decide +kernel

theorem checked_39808 : Scan.checkChunk context facts instructions 39808 128 = true := by
  decide +kernel

theorem checked_39936 : Scan.checkChunk context facts instructions 39936 128 = true := by
  decide +kernel

theorem checked_40064 : Scan.checkChunk context facts instructions 40064 128 = true := by
  decide +kernel

theorem checked_40192 : Scan.checkChunk context facts instructions 40192 128 = true := by
  decide +kernel

theorem checked_40320 : Scan.checkChunk context facts instructions 40320 128 = true := by
  decide +kernel

theorem checked_40448 : Scan.checkChunk context facts instructions 40448 128 = true := by
  decide +kernel

theorem checked_40576 : Scan.checkChunk context facts instructions 40576 128 = true := by
  decide +kernel

theorem checked_40704 : Scan.checkChunk context facts instructions 40704 128 = true := by
  decide +kernel

theorem checked_40832 : Scan.checkChunk context facts instructions 40832 128 = true := by
  decide +kernel

theorem holds_40960 (hr : ∀ r : Fin 4, eval subgroupGenerator (extraRelatorWord r) = 1) :
    ∀ n, n < 40960 → Holds smallSubgroup subgroupGenerator (definitions.repr subgroupGenerator) (facts n) := by
  have h36992 := Scan.chunk_sound (context_valid hr) facts instructions
    36864 128 (holds_36864 hr) checked_36864
  have h37120 := Scan.chunk_sound (context_valid hr) facts instructions
    36992 128 h36992 checked_36992
  have h37248 := Scan.chunk_sound (context_valid hr) facts instructions
    37120 128 h37120 checked_37120
  have h37376 := Scan.chunk_sound (context_valid hr) facts instructions
    37248 128 h37248 checked_37248
  have h37504 := Scan.chunk_sound (context_valid hr) facts instructions
    37376 128 h37376 checked_37376
  have h37632 := Scan.chunk_sound (context_valid hr) facts instructions
    37504 128 h37504 checked_37504
  have h37760 := Scan.chunk_sound (context_valid hr) facts instructions
    37632 128 h37632 checked_37632
  have h37888 := Scan.chunk_sound (context_valid hr) facts instructions
    37760 128 h37760 checked_37760
  have h38016 := Scan.chunk_sound (context_valid hr) facts instructions
    37888 128 h37888 checked_37888
  have h38144 := Scan.chunk_sound (context_valid hr) facts instructions
    38016 128 h38016 checked_38016
  have h38272 := Scan.chunk_sound (context_valid hr) facts instructions
    38144 128 h38144 checked_38144
  have h38400 := Scan.chunk_sound (context_valid hr) facts instructions
    38272 128 h38272 checked_38272
  have h38528 := Scan.chunk_sound (context_valid hr) facts instructions
    38400 128 h38400 checked_38400
  have h38656 := Scan.chunk_sound (context_valid hr) facts instructions
    38528 128 h38528 checked_38528
  have h38784 := Scan.chunk_sound (context_valid hr) facts instructions
    38656 128 h38656 checked_38656
  have h38912 := Scan.chunk_sound (context_valid hr) facts instructions
    38784 128 h38784 checked_38784
  have h39040 := Scan.chunk_sound (context_valid hr) facts instructions
    38912 128 h38912 checked_38912
  have h39168 := Scan.chunk_sound (context_valid hr) facts instructions
    39040 128 h39040 checked_39040
  have h39296 := Scan.chunk_sound (context_valid hr) facts instructions
    39168 128 h39168 checked_39168
  have h39424 := Scan.chunk_sound (context_valid hr) facts instructions
    39296 128 h39296 checked_39296
  have h39552 := Scan.chunk_sound (context_valid hr) facts instructions
    39424 128 h39424 checked_39424
  have h39680 := Scan.chunk_sound (context_valid hr) facts instructions
    39552 128 h39552 checked_39552
  have h39808 := Scan.chunk_sound (context_valid hr) facts instructions
    39680 128 h39680 checked_39680
  have h39936 := Scan.chunk_sound (context_valid hr) facts instructions
    39808 128 h39808 checked_39808
  have h40064 := Scan.chunk_sound (context_valid hr) facts instructions
    39936 128 h39936 checked_39936
  have h40192 := Scan.chunk_sound (context_valid hr) facts instructions
    40064 128 h40064 checked_40064
  have h40320 := Scan.chunk_sound (context_valid hr) facts instructions
    40192 128 h40192 checked_40192
  have h40448 := Scan.chunk_sound (context_valid hr) facts instructions
    40320 128 h40320 checked_40320
  have h40576 := Scan.chunk_sound (context_valid hr) facts instructions
    40448 128 h40448 checked_40448
  have h40704 := Scan.chunk_sound (context_valid hr) facts instructions
    40576 128 h40576 checked_40576
  have h40832 := Scan.chunk_sound (context_valid hr) facts instructions
    40704 128 h40704 checked_40704
  have h40960 := Scan.chunk_sound (context_valid hr) facts instructions
    40832 128 h40832 checked_40832
  exact h40960

end Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced.Bound.LocalFinite.Certificate
