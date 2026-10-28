module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.M1aBound.FiniteBound.Reduced.Bound.LocalFinite.Checks06

/-! Kernel checks for the conditional local coset certificate.
Each accepted step is an actual word deduction. The four relator identities
remain explicit premises; see `source/README.md`. -/

@[expose] public section
namespace Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced.Bound.LocalFinite.Certificate
open Subgroup.CosetWordCertificate

theorem checked_28672 : Scan.checkChunk context facts instructions 28672 128 = true := by
  decide +kernel

theorem checked_28800 : Scan.checkChunk context facts instructions 28800 128 = true := by
  decide +kernel

theorem checked_28928 : Scan.checkChunk context facts instructions 28928 128 = true := by
  decide +kernel

theorem checked_29056 : Scan.checkChunk context facts instructions 29056 128 = true := by
  decide +kernel

theorem checked_29184 : Scan.checkChunk context facts instructions 29184 128 = true := by
  decide +kernel

theorem checked_29312 : Scan.checkChunk context facts instructions 29312 128 = true := by
  decide +kernel

theorem checked_29440 : Scan.checkChunk context facts instructions 29440 128 = true := by
  decide +kernel

theorem checked_29568 : Scan.checkChunk context facts instructions 29568 128 = true := by
  decide +kernel

theorem checked_29696 : Scan.checkChunk context facts instructions 29696 128 = true := by
  decide +kernel

theorem checked_29824 : Scan.checkChunk context facts instructions 29824 128 = true := by
  decide +kernel

theorem checked_29952 : Scan.checkChunk context facts instructions 29952 128 = true := by
  decide +kernel

theorem checked_30080 : Scan.checkChunk context facts instructions 30080 128 = true := by
  decide +kernel

theorem checked_30208 : Scan.checkChunk context facts instructions 30208 128 = true := by
  decide +kernel

theorem checked_30336 : Scan.checkChunk context facts instructions 30336 128 = true := by
  decide +kernel

theorem checked_30464 : Scan.checkChunk context facts instructions 30464 128 = true := by
  decide +kernel

theorem checked_30592 : Scan.checkChunk context facts instructions 30592 128 = true := by
  decide +kernel

theorem checked_30720 : Scan.checkChunk context facts instructions 30720 128 = true := by
  decide +kernel

theorem checked_30848 : Scan.checkChunk context facts instructions 30848 128 = true := by
  decide +kernel

theorem checked_30976 : Scan.checkChunk context facts instructions 30976 128 = true := by
  decide +kernel

theorem checked_31104 : Scan.checkChunk context facts instructions 31104 128 = true := by
  decide +kernel

theorem checked_31232 : Scan.checkChunk context facts instructions 31232 128 = true := by
  decide +kernel

theorem checked_31360 : Scan.checkChunk context facts instructions 31360 128 = true := by
  decide +kernel

theorem checked_31488 : Scan.checkChunk context facts instructions 31488 128 = true := by
  decide +kernel

theorem checked_31616 : Scan.checkChunk context facts instructions 31616 128 = true := by
  decide +kernel

theorem checked_31744 : Scan.checkChunk context facts instructions 31744 128 = true := by
  decide +kernel

theorem checked_31872 : Scan.checkChunk context facts instructions 31872 128 = true := by
  decide +kernel

theorem checked_32000 : Scan.checkChunk context facts instructions 32000 128 = true := by
  decide +kernel

theorem checked_32128 : Scan.checkChunk context facts instructions 32128 128 = true := by
  decide +kernel

theorem checked_32256 : Scan.checkChunk context facts instructions 32256 128 = true := by
  decide +kernel

theorem checked_32384 : Scan.checkChunk context facts instructions 32384 128 = true := by
  decide +kernel

theorem checked_32512 : Scan.checkChunk context facts instructions 32512 128 = true := by
  decide +kernel

theorem checked_32640 : Scan.checkChunk context facts instructions 32640 128 = true := by
  decide +kernel

theorem holds_32768 (hr : ∀ r : Fin 4, eval subgroupGenerator (extraRelatorWord r) = 1) :
    ∀ n, n < 32768 → Holds smallSubgroup subgroupGenerator (definitions.repr subgroupGenerator) (facts n) := by
  have h28800 := Scan.chunk_sound (context_valid hr) facts instructions
    28672 128 (holds_28672 hr) checked_28672
  have h28928 := Scan.chunk_sound (context_valid hr) facts instructions
    28800 128 h28800 checked_28800
  have h29056 := Scan.chunk_sound (context_valid hr) facts instructions
    28928 128 h28928 checked_28928
  have h29184 := Scan.chunk_sound (context_valid hr) facts instructions
    29056 128 h29056 checked_29056
  have h29312 := Scan.chunk_sound (context_valid hr) facts instructions
    29184 128 h29184 checked_29184
  have h29440 := Scan.chunk_sound (context_valid hr) facts instructions
    29312 128 h29312 checked_29312
  have h29568 := Scan.chunk_sound (context_valid hr) facts instructions
    29440 128 h29440 checked_29440
  have h29696 := Scan.chunk_sound (context_valid hr) facts instructions
    29568 128 h29568 checked_29568
  have h29824 := Scan.chunk_sound (context_valid hr) facts instructions
    29696 128 h29696 checked_29696
  have h29952 := Scan.chunk_sound (context_valid hr) facts instructions
    29824 128 h29824 checked_29824
  have h30080 := Scan.chunk_sound (context_valid hr) facts instructions
    29952 128 h29952 checked_29952
  have h30208 := Scan.chunk_sound (context_valid hr) facts instructions
    30080 128 h30080 checked_30080
  have h30336 := Scan.chunk_sound (context_valid hr) facts instructions
    30208 128 h30208 checked_30208
  have h30464 := Scan.chunk_sound (context_valid hr) facts instructions
    30336 128 h30336 checked_30336
  have h30592 := Scan.chunk_sound (context_valid hr) facts instructions
    30464 128 h30464 checked_30464
  have h30720 := Scan.chunk_sound (context_valid hr) facts instructions
    30592 128 h30592 checked_30592
  have h30848 := Scan.chunk_sound (context_valid hr) facts instructions
    30720 128 h30720 checked_30720
  have h30976 := Scan.chunk_sound (context_valid hr) facts instructions
    30848 128 h30848 checked_30848
  have h31104 := Scan.chunk_sound (context_valid hr) facts instructions
    30976 128 h30976 checked_30976
  have h31232 := Scan.chunk_sound (context_valid hr) facts instructions
    31104 128 h31104 checked_31104
  have h31360 := Scan.chunk_sound (context_valid hr) facts instructions
    31232 128 h31232 checked_31232
  have h31488 := Scan.chunk_sound (context_valid hr) facts instructions
    31360 128 h31360 checked_31360
  have h31616 := Scan.chunk_sound (context_valid hr) facts instructions
    31488 128 h31488 checked_31488
  have h31744 := Scan.chunk_sound (context_valid hr) facts instructions
    31616 128 h31616 checked_31616
  have h31872 := Scan.chunk_sound (context_valid hr) facts instructions
    31744 128 h31744 checked_31744
  have h32000 := Scan.chunk_sound (context_valid hr) facts instructions
    31872 128 h31872 checked_31872
  have h32128 := Scan.chunk_sound (context_valid hr) facts instructions
    32000 128 h32000 checked_32000
  have h32256 := Scan.chunk_sound (context_valid hr) facts instructions
    32128 128 h32128 checked_32128
  have h32384 := Scan.chunk_sound (context_valid hr) facts instructions
    32256 128 h32256 checked_32256
  have h32512 := Scan.chunk_sound (context_valid hr) facts instructions
    32384 128 h32384 checked_32384
  have h32640 := Scan.chunk_sound (context_valid hr) facts instructions
    32512 128 h32512 checked_32512
  have h32768 := Scan.chunk_sound (context_valid hr) facts instructions
    32640 128 h32640 checked_32640
  exact h32768

end Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced.Bound.LocalFinite.Certificate
