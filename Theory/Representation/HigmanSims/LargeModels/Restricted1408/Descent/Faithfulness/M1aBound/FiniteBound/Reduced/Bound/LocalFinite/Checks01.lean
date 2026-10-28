module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.M1aBound.FiniteBound.Reduced.Bound.LocalFinite.Checks00

/-! Kernel checks for the conditional local coset certificate.
Each accepted step is an actual word deduction. The four relator identities
remain explicit premises; see `source/README.md`. -/

@[expose] public section
namespace Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced.Bound.LocalFinite.Certificate
open Subgroup.CosetWordCertificate

theorem checked_4096 : Scan.checkChunk context facts instructions 4096 128 = true := by
  decide +kernel

theorem checked_4224 : Scan.checkChunk context facts instructions 4224 128 = true := by
  decide +kernel

theorem checked_4352 : Scan.checkChunk context facts instructions 4352 128 = true := by
  decide +kernel

theorem checked_4480 : Scan.checkChunk context facts instructions 4480 128 = true := by
  decide +kernel

theorem checked_4608 : Scan.checkChunk context facts instructions 4608 128 = true := by
  decide +kernel

theorem checked_4736 : Scan.checkChunk context facts instructions 4736 128 = true := by
  decide +kernel

theorem checked_4864 : Scan.checkChunk context facts instructions 4864 128 = true := by
  decide +kernel

theorem checked_4992 : Scan.checkChunk context facts instructions 4992 128 = true := by
  decide +kernel

theorem checked_5120 : Scan.checkChunk context facts instructions 5120 128 = true := by
  decide +kernel

theorem checked_5248 : Scan.checkChunk context facts instructions 5248 128 = true := by
  decide +kernel

theorem checked_5376 : Scan.checkChunk context facts instructions 5376 128 = true := by
  decide +kernel

theorem checked_5504 : Scan.checkChunk context facts instructions 5504 128 = true := by
  decide +kernel

theorem checked_5632 : Scan.checkChunk context facts instructions 5632 128 = true := by
  decide +kernel

theorem checked_5760 : Scan.checkChunk context facts instructions 5760 128 = true := by
  decide +kernel

theorem checked_5888 : Scan.checkChunk context facts instructions 5888 128 = true := by
  decide +kernel

theorem checked_6016 : Scan.checkChunk context facts instructions 6016 128 = true := by
  decide +kernel

theorem checked_6144 : Scan.checkChunk context facts instructions 6144 128 = true := by
  decide +kernel

theorem checked_6272 : Scan.checkChunk context facts instructions 6272 128 = true := by
  decide +kernel

theorem checked_6400 : Scan.checkChunk context facts instructions 6400 128 = true := by
  decide +kernel

theorem checked_6528 : Scan.checkChunk context facts instructions 6528 128 = true := by
  decide +kernel

theorem checked_6656 : Scan.checkChunk context facts instructions 6656 128 = true := by
  decide +kernel

theorem checked_6784 : Scan.checkChunk context facts instructions 6784 128 = true := by
  decide +kernel

theorem checked_6912 : Scan.checkChunk context facts instructions 6912 128 = true := by
  decide +kernel

theorem checked_7040 : Scan.checkChunk context facts instructions 7040 128 = true := by
  decide +kernel

theorem checked_7168 : Scan.checkChunk context facts instructions 7168 128 = true := by
  decide +kernel

theorem checked_7296 : Scan.checkChunk context facts instructions 7296 128 = true := by
  decide +kernel

theorem checked_7424 : Scan.checkChunk context facts instructions 7424 128 = true := by
  decide +kernel

theorem checked_7552 : Scan.checkChunk context facts instructions 7552 128 = true := by
  decide +kernel

theorem checked_7680 : Scan.checkChunk context facts instructions 7680 128 = true := by
  decide +kernel

theorem checked_7808 : Scan.checkChunk context facts instructions 7808 128 = true := by
  decide +kernel

theorem checked_7936 : Scan.checkChunk context facts instructions 7936 128 = true := by
  decide +kernel

theorem checked_8064 : Scan.checkChunk context facts instructions 8064 128 = true := by
  decide +kernel

theorem holds_8192 (hr : ∀ r : Fin 4, eval subgroupGenerator (extraRelatorWord r) = 1) :
    ∀ n, n < 8192 → Holds smallSubgroup subgroupGenerator (definitions.repr subgroupGenerator) (facts n) := by
  have h4224 := Scan.chunk_sound (context_valid hr) facts instructions
    4096 128 (holds_4096 hr) checked_4096
  have h4352 := Scan.chunk_sound (context_valid hr) facts instructions
    4224 128 h4224 checked_4224
  have h4480 := Scan.chunk_sound (context_valid hr) facts instructions
    4352 128 h4352 checked_4352
  have h4608 := Scan.chunk_sound (context_valid hr) facts instructions
    4480 128 h4480 checked_4480
  have h4736 := Scan.chunk_sound (context_valid hr) facts instructions
    4608 128 h4608 checked_4608
  have h4864 := Scan.chunk_sound (context_valid hr) facts instructions
    4736 128 h4736 checked_4736
  have h4992 := Scan.chunk_sound (context_valid hr) facts instructions
    4864 128 h4864 checked_4864
  have h5120 := Scan.chunk_sound (context_valid hr) facts instructions
    4992 128 h4992 checked_4992
  have h5248 := Scan.chunk_sound (context_valid hr) facts instructions
    5120 128 h5120 checked_5120
  have h5376 := Scan.chunk_sound (context_valid hr) facts instructions
    5248 128 h5248 checked_5248
  have h5504 := Scan.chunk_sound (context_valid hr) facts instructions
    5376 128 h5376 checked_5376
  have h5632 := Scan.chunk_sound (context_valid hr) facts instructions
    5504 128 h5504 checked_5504
  have h5760 := Scan.chunk_sound (context_valid hr) facts instructions
    5632 128 h5632 checked_5632
  have h5888 := Scan.chunk_sound (context_valid hr) facts instructions
    5760 128 h5760 checked_5760
  have h6016 := Scan.chunk_sound (context_valid hr) facts instructions
    5888 128 h5888 checked_5888
  have h6144 := Scan.chunk_sound (context_valid hr) facts instructions
    6016 128 h6016 checked_6016
  have h6272 := Scan.chunk_sound (context_valid hr) facts instructions
    6144 128 h6144 checked_6144
  have h6400 := Scan.chunk_sound (context_valid hr) facts instructions
    6272 128 h6272 checked_6272
  have h6528 := Scan.chunk_sound (context_valid hr) facts instructions
    6400 128 h6400 checked_6400
  have h6656 := Scan.chunk_sound (context_valid hr) facts instructions
    6528 128 h6528 checked_6528
  have h6784 := Scan.chunk_sound (context_valid hr) facts instructions
    6656 128 h6656 checked_6656
  have h6912 := Scan.chunk_sound (context_valid hr) facts instructions
    6784 128 h6784 checked_6784
  have h7040 := Scan.chunk_sound (context_valid hr) facts instructions
    6912 128 h6912 checked_6912
  have h7168 := Scan.chunk_sound (context_valid hr) facts instructions
    7040 128 h7040 checked_7040
  have h7296 := Scan.chunk_sound (context_valid hr) facts instructions
    7168 128 h7168 checked_7168
  have h7424 := Scan.chunk_sound (context_valid hr) facts instructions
    7296 128 h7296 checked_7296
  have h7552 := Scan.chunk_sound (context_valid hr) facts instructions
    7424 128 h7424 checked_7424
  have h7680 := Scan.chunk_sound (context_valid hr) facts instructions
    7552 128 h7552 checked_7552
  have h7808 := Scan.chunk_sound (context_valid hr) facts instructions
    7680 128 h7680 checked_7680
  have h7936 := Scan.chunk_sound (context_valid hr) facts instructions
    7808 128 h7808 checked_7808
  have h8064 := Scan.chunk_sound (context_valid hr) facts instructions
    7936 128 h7936 checked_7936
  have h8192 := Scan.chunk_sound (context_valid hr) facts instructions
    8064 128 h8064 checked_8064
  exact h8192

end Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced.Bound.LocalFinite.Certificate
