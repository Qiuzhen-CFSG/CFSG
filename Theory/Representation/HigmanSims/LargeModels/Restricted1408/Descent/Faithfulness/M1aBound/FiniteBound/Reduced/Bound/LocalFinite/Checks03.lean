module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.M1aBound.FiniteBound.Reduced.Bound.LocalFinite.Checks02

/-! Kernel checks for the conditional local coset certificate.
Each accepted step is an actual word deduction. The four relator identities
remain explicit premises; see `source/README.md`. -/

@[expose] public section
namespace Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced.Bound.LocalFinite.Certificate
open Subgroup.CosetWordCertificate

theorem checked_12288 : Scan.checkChunk context facts instructions 12288 128 = true := by
  decide +kernel

theorem checked_12416 : Scan.checkChunk context facts instructions 12416 128 = true := by
  decide +kernel

theorem checked_12544 : Scan.checkChunk context facts instructions 12544 128 = true := by
  decide +kernel

theorem checked_12672 : Scan.checkChunk context facts instructions 12672 128 = true := by
  decide +kernel

theorem checked_12800 : Scan.checkChunk context facts instructions 12800 128 = true := by
  decide +kernel

theorem checked_12928 : Scan.checkChunk context facts instructions 12928 128 = true := by
  decide +kernel

theorem checked_13056 : Scan.checkChunk context facts instructions 13056 128 = true := by
  decide +kernel

theorem checked_13184 : Scan.checkChunk context facts instructions 13184 128 = true := by
  decide +kernel

theorem checked_13312 : Scan.checkChunk context facts instructions 13312 128 = true := by
  decide +kernel

theorem checked_13440 : Scan.checkChunk context facts instructions 13440 128 = true := by
  decide +kernel

theorem checked_13568 : Scan.checkChunk context facts instructions 13568 128 = true := by
  decide +kernel

theorem checked_13696 : Scan.checkChunk context facts instructions 13696 128 = true := by
  decide +kernel

theorem checked_13824 : Scan.checkChunk context facts instructions 13824 128 = true := by
  decide +kernel

theorem checked_13952 : Scan.checkChunk context facts instructions 13952 128 = true := by
  decide +kernel

theorem checked_14080 : Scan.checkChunk context facts instructions 14080 128 = true := by
  decide +kernel

theorem checked_14208 : Scan.checkChunk context facts instructions 14208 128 = true := by
  decide +kernel

theorem checked_14336 : Scan.checkChunk context facts instructions 14336 128 = true := by
  decide +kernel

theorem checked_14464 : Scan.checkChunk context facts instructions 14464 128 = true := by
  decide +kernel

theorem checked_14592 : Scan.checkChunk context facts instructions 14592 128 = true := by
  decide +kernel

theorem checked_14720 : Scan.checkChunk context facts instructions 14720 128 = true := by
  decide +kernel

theorem checked_14848 : Scan.checkChunk context facts instructions 14848 128 = true := by
  decide +kernel

theorem checked_14976 : Scan.checkChunk context facts instructions 14976 128 = true := by
  decide +kernel

theorem checked_15104 : Scan.checkChunk context facts instructions 15104 128 = true := by
  decide +kernel

theorem checked_15232 : Scan.checkChunk context facts instructions 15232 128 = true := by
  decide +kernel

theorem checked_15360 : Scan.checkChunk context facts instructions 15360 128 = true := by
  decide +kernel

theorem checked_15488 : Scan.checkChunk context facts instructions 15488 128 = true := by
  decide +kernel

theorem checked_15616 : Scan.checkChunk context facts instructions 15616 128 = true := by
  decide +kernel

theorem checked_15744 : Scan.checkChunk context facts instructions 15744 128 = true := by
  decide +kernel

theorem checked_15872 : Scan.checkChunk context facts instructions 15872 128 = true := by
  decide +kernel

theorem checked_16000 : Scan.checkChunk context facts instructions 16000 128 = true := by
  decide +kernel

theorem checked_16128 : Scan.checkChunk context facts instructions 16128 128 = true := by
  decide +kernel

theorem checked_16256 : Scan.checkChunk context facts instructions 16256 128 = true := by
  decide +kernel

theorem holds_16384 (hr : ∀ r : Fin 4, eval subgroupGenerator (extraRelatorWord r) = 1) :
    ∀ n, n < 16384 → Holds smallSubgroup subgroupGenerator (definitions.repr subgroupGenerator) (facts n) := by
  have h12416 := Scan.chunk_sound (context_valid hr) facts instructions
    12288 128 (holds_12288 hr) checked_12288
  have h12544 := Scan.chunk_sound (context_valid hr) facts instructions
    12416 128 h12416 checked_12416
  have h12672 := Scan.chunk_sound (context_valid hr) facts instructions
    12544 128 h12544 checked_12544
  have h12800 := Scan.chunk_sound (context_valid hr) facts instructions
    12672 128 h12672 checked_12672
  have h12928 := Scan.chunk_sound (context_valid hr) facts instructions
    12800 128 h12800 checked_12800
  have h13056 := Scan.chunk_sound (context_valid hr) facts instructions
    12928 128 h12928 checked_12928
  have h13184 := Scan.chunk_sound (context_valid hr) facts instructions
    13056 128 h13056 checked_13056
  have h13312 := Scan.chunk_sound (context_valid hr) facts instructions
    13184 128 h13184 checked_13184
  have h13440 := Scan.chunk_sound (context_valid hr) facts instructions
    13312 128 h13312 checked_13312
  have h13568 := Scan.chunk_sound (context_valid hr) facts instructions
    13440 128 h13440 checked_13440
  have h13696 := Scan.chunk_sound (context_valid hr) facts instructions
    13568 128 h13568 checked_13568
  have h13824 := Scan.chunk_sound (context_valid hr) facts instructions
    13696 128 h13696 checked_13696
  have h13952 := Scan.chunk_sound (context_valid hr) facts instructions
    13824 128 h13824 checked_13824
  have h14080 := Scan.chunk_sound (context_valid hr) facts instructions
    13952 128 h13952 checked_13952
  have h14208 := Scan.chunk_sound (context_valid hr) facts instructions
    14080 128 h14080 checked_14080
  have h14336 := Scan.chunk_sound (context_valid hr) facts instructions
    14208 128 h14208 checked_14208
  have h14464 := Scan.chunk_sound (context_valid hr) facts instructions
    14336 128 h14336 checked_14336
  have h14592 := Scan.chunk_sound (context_valid hr) facts instructions
    14464 128 h14464 checked_14464
  have h14720 := Scan.chunk_sound (context_valid hr) facts instructions
    14592 128 h14592 checked_14592
  have h14848 := Scan.chunk_sound (context_valid hr) facts instructions
    14720 128 h14720 checked_14720
  have h14976 := Scan.chunk_sound (context_valid hr) facts instructions
    14848 128 h14848 checked_14848
  have h15104 := Scan.chunk_sound (context_valid hr) facts instructions
    14976 128 h14976 checked_14976
  have h15232 := Scan.chunk_sound (context_valid hr) facts instructions
    15104 128 h15104 checked_15104
  have h15360 := Scan.chunk_sound (context_valid hr) facts instructions
    15232 128 h15232 checked_15232
  have h15488 := Scan.chunk_sound (context_valid hr) facts instructions
    15360 128 h15360 checked_15360
  have h15616 := Scan.chunk_sound (context_valid hr) facts instructions
    15488 128 h15488 checked_15488
  have h15744 := Scan.chunk_sound (context_valid hr) facts instructions
    15616 128 h15616 checked_15616
  have h15872 := Scan.chunk_sound (context_valid hr) facts instructions
    15744 128 h15744 checked_15744
  have h16000 := Scan.chunk_sound (context_valid hr) facts instructions
    15872 128 h15872 checked_15872
  have h16128 := Scan.chunk_sound (context_valid hr) facts instructions
    16000 128 h16000 checked_16000
  have h16256 := Scan.chunk_sound (context_valid hr) facts instructions
    16128 128 h16128 checked_16128
  have h16384 := Scan.chunk_sound (context_valid hr) facts instructions
    16256 128 h16256 checked_16256
  exact h16384

end Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced.Bound.LocalFinite.Certificate
