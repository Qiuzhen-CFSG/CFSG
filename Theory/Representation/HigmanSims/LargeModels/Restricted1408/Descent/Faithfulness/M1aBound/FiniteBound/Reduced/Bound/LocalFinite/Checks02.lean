module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.M1aBound.FiniteBound.Reduced.Bound.LocalFinite.Checks01

/-! Kernel checks for the conditional local coset certificate.
Each accepted step is an actual word deduction. The four relator identities
remain explicit premises; see `source/README.md`. -/

@[expose] public section
namespace Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced.Bound.LocalFinite.Certificate
open Subgroup.CosetWordCertificate

theorem checked_8192 : Scan.checkChunk context facts instructions 8192 128 = true := by
  decide +kernel

theorem checked_8320 : Scan.checkChunk context facts instructions 8320 128 = true := by
  decide +kernel

theorem checked_8448 : Scan.checkChunk context facts instructions 8448 128 = true := by
  decide +kernel

theorem checked_8576 : Scan.checkChunk context facts instructions 8576 128 = true := by
  decide +kernel

theorem checked_8704 : Scan.checkChunk context facts instructions 8704 128 = true := by
  decide +kernel

theorem checked_8832 : Scan.checkChunk context facts instructions 8832 128 = true := by
  decide +kernel

theorem checked_8960 : Scan.checkChunk context facts instructions 8960 128 = true := by
  decide +kernel

theorem checked_9088 : Scan.checkChunk context facts instructions 9088 128 = true := by
  decide +kernel

theorem checked_9216 : Scan.checkChunk context facts instructions 9216 128 = true := by
  decide +kernel

theorem checked_9344 : Scan.checkChunk context facts instructions 9344 128 = true := by
  decide +kernel

theorem checked_9472 : Scan.checkChunk context facts instructions 9472 128 = true := by
  decide +kernel

theorem checked_9600 : Scan.checkChunk context facts instructions 9600 128 = true := by
  decide +kernel

theorem checked_9728 : Scan.checkChunk context facts instructions 9728 128 = true := by
  decide +kernel

theorem checked_9856 : Scan.checkChunk context facts instructions 9856 128 = true := by
  decide +kernel

theorem checked_9984 : Scan.checkChunk context facts instructions 9984 128 = true := by
  decide +kernel

theorem checked_10112 : Scan.checkChunk context facts instructions 10112 128 = true := by
  decide +kernel

theorem checked_10240 : Scan.checkChunk context facts instructions 10240 128 = true := by
  decide +kernel

theorem checked_10368 : Scan.checkChunk context facts instructions 10368 128 = true := by
  decide +kernel

theorem checked_10496 : Scan.checkChunk context facts instructions 10496 128 = true := by
  decide +kernel

theorem checked_10624 : Scan.checkChunk context facts instructions 10624 128 = true := by
  decide +kernel

theorem checked_10752 : Scan.checkChunk context facts instructions 10752 128 = true := by
  decide +kernel

theorem checked_10880 : Scan.checkChunk context facts instructions 10880 128 = true := by
  decide +kernel

theorem checked_11008 : Scan.checkChunk context facts instructions 11008 128 = true := by
  decide +kernel

theorem checked_11136 : Scan.checkChunk context facts instructions 11136 128 = true := by
  decide +kernel

theorem checked_11264 : Scan.checkChunk context facts instructions 11264 128 = true := by
  decide +kernel

theorem checked_11392 : Scan.checkChunk context facts instructions 11392 128 = true := by
  decide +kernel

theorem checked_11520 : Scan.checkChunk context facts instructions 11520 128 = true := by
  decide +kernel

theorem checked_11648 : Scan.checkChunk context facts instructions 11648 128 = true := by
  decide +kernel

theorem checked_11776 : Scan.checkChunk context facts instructions 11776 128 = true := by
  decide +kernel

theorem checked_11904 : Scan.checkChunk context facts instructions 11904 128 = true := by
  decide +kernel

theorem checked_12032 : Scan.checkChunk context facts instructions 12032 128 = true := by
  decide +kernel

theorem checked_12160 : Scan.checkChunk context facts instructions 12160 128 = true := by
  decide +kernel

theorem holds_12288 (hr : ∀ r : Fin 4, eval subgroupGenerator (extraRelatorWord r) = 1) :
    ∀ n, n < 12288 → Holds smallSubgroup subgroupGenerator (definitions.repr subgroupGenerator) (facts n) := by
  have h8320 := Scan.chunk_sound (context_valid hr) facts instructions
    8192 128 (holds_8192 hr) checked_8192
  have h8448 := Scan.chunk_sound (context_valid hr) facts instructions
    8320 128 h8320 checked_8320
  have h8576 := Scan.chunk_sound (context_valid hr) facts instructions
    8448 128 h8448 checked_8448
  have h8704 := Scan.chunk_sound (context_valid hr) facts instructions
    8576 128 h8576 checked_8576
  have h8832 := Scan.chunk_sound (context_valid hr) facts instructions
    8704 128 h8704 checked_8704
  have h8960 := Scan.chunk_sound (context_valid hr) facts instructions
    8832 128 h8832 checked_8832
  have h9088 := Scan.chunk_sound (context_valid hr) facts instructions
    8960 128 h8960 checked_8960
  have h9216 := Scan.chunk_sound (context_valid hr) facts instructions
    9088 128 h9088 checked_9088
  have h9344 := Scan.chunk_sound (context_valid hr) facts instructions
    9216 128 h9216 checked_9216
  have h9472 := Scan.chunk_sound (context_valid hr) facts instructions
    9344 128 h9344 checked_9344
  have h9600 := Scan.chunk_sound (context_valid hr) facts instructions
    9472 128 h9472 checked_9472
  have h9728 := Scan.chunk_sound (context_valid hr) facts instructions
    9600 128 h9600 checked_9600
  have h9856 := Scan.chunk_sound (context_valid hr) facts instructions
    9728 128 h9728 checked_9728
  have h9984 := Scan.chunk_sound (context_valid hr) facts instructions
    9856 128 h9856 checked_9856
  have h10112 := Scan.chunk_sound (context_valid hr) facts instructions
    9984 128 h9984 checked_9984
  have h10240 := Scan.chunk_sound (context_valid hr) facts instructions
    10112 128 h10112 checked_10112
  have h10368 := Scan.chunk_sound (context_valid hr) facts instructions
    10240 128 h10240 checked_10240
  have h10496 := Scan.chunk_sound (context_valid hr) facts instructions
    10368 128 h10368 checked_10368
  have h10624 := Scan.chunk_sound (context_valid hr) facts instructions
    10496 128 h10496 checked_10496
  have h10752 := Scan.chunk_sound (context_valid hr) facts instructions
    10624 128 h10624 checked_10624
  have h10880 := Scan.chunk_sound (context_valid hr) facts instructions
    10752 128 h10752 checked_10752
  have h11008 := Scan.chunk_sound (context_valid hr) facts instructions
    10880 128 h10880 checked_10880
  have h11136 := Scan.chunk_sound (context_valid hr) facts instructions
    11008 128 h11008 checked_11008
  have h11264 := Scan.chunk_sound (context_valid hr) facts instructions
    11136 128 h11136 checked_11136
  have h11392 := Scan.chunk_sound (context_valid hr) facts instructions
    11264 128 h11264 checked_11264
  have h11520 := Scan.chunk_sound (context_valid hr) facts instructions
    11392 128 h11392 checked_11392
  have h11648 := Scan.chunk_sound (context_valid hr) facts instructions
    11520 128 h11520 checked_11520
  have h11776 := Scan.chunk_sound (context_valid hr) facts instructions
    11648 128 h11648 checked_11648
  have h11904 := Scan.chunk_sound (context_valid hr) facts instructions
    11776 128 h11776 checked_11776
  have h12032 := Scan.chunk_sound (context_valid hr) facts instructions
    11904 128 h11904 checked_11904
  have h12160 := Scan.chunk_sound (context_valid hr) facts instructions
    12032 128 h12032 checked_12032
  have h12288 := Scan.chunk_sound (context_valid hr) facts instructions
    12160 128 h12160 checked_12160
  exact h12288

end Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced.Bound.LocalFinite.Certificate
