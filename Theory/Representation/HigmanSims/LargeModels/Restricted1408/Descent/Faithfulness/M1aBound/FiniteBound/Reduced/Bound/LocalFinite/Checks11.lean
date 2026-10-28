module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.M1aBound.FiniteBound.Reduced.Bound.LocalFinite.Checks10

/-! Kernel checks for the conditional local coset certificate.
Each accepted step is an actual word deduction. The four relator identities
remain explicit premises; see `source/README.md`. -/

@[expose] public section
namespace Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced.Bound.LocalFinite.Certificate
open Subgroup.CosetWordCertificate

theorem checked_45056 : Scan.checkChunk context facts instructions 45056 128 = true := by
  decide +kernel

theorem checked_45184 : Scan.checkChunk context facts instructions 45184 128 = true := by
  decide +kernel

theorem checked_45312 : Scan.checkChunk context facts instructions 45312 128 = true := by
  decide +kernel

theorem checked_45440 : Scan.checkChunk context facts instructions 45440 128 = true := by
  decide +kernel

theorem checked_45568 : Scan.checkChunk context facts instructions 45568 128 = true := by
  decide +kernel

theorem checked_45696 : Scan.checkChunk context facts instructions 45696 128 = true := by
  decide +kernel

theorem checked_45824 : Scan.checkChunk context facts instructions 45824 128 = true := by
  decide +kernel

theorem checked_45952 : Scan.checkChunk context facts instructions 45952 128 = true := by
  decide +kernel

theorem checked_46080 : Scan.checkChunk context facts instructions 46080 128 = true := by
  decide +kernel

theorem checked_46208 : Scan.checkChunk context facts instructions 46208 128 = true := by
  decide +kernel

theorem checked_46336 : Scan.checkChunk context facts instructions 46336 128 = true := by
  decide +kernel

theorem checked_46464 : Scan.checkChunk context facts instructions 46464 128 = true := by
  decide +kernel

theorem checked_46592 : Scan.checkChunk context facts instructions 46592 128 = true := by
  decide +kernel

theorem checked_46720 : Scan.checkChunk context facts instructions 46720 128 = true := by
  decide +kernel

theorem checked_46848 : Scan.checkChunk context facts instructions 46848 128 = true := by
  decide +kernel

theorem checked_46976 : Scan.checkChunk context facts instructions 46976 128 = true := by
  decide +kernel

theorem checked_47104 : Scan.checkChunk context facts instructions 47104 128 = true := by
  decide +kernel

theorem checked_47232 : Scan.checkChunk context facts instructions 47232 128 = true := by
  decide +kernel

theorem checked_47360 : Scan.checkChunk context facts instructions 47360 128 = true := by
  decide +kernel

theorem checked_47488 : Scan.checkChunk context facts instructions 47488 128 = true := by
  decide +kernel

theorem checked_47616 : Scan.checkChunk context facts instructions 47616 128 = true := by
  decide +kernel

theorem checked_47744 : Scan.checkChunk context facts instructions 47744 128 = true := by
  decide +kernel

theorem checked_47872 : Scan.checkChunk context facts instructions 47872 128 = true := by
  decide +kernel

theorem checked_48000 : Scan.checkChunk context facts instructions 48000 128 = true := by
  decide +kernel

theorem checked_48128 : Scan.checkChunk context facts instructions 48128 128 = true := by
  decide +kernel

theorem checked_48256 : Scan.checkChunk context facts instructions 48256 128 = true := by
  decide +kernel

theorem checked_48384 : Scan.checkChunk context facts instructions 48384 128 = true := by
  decide +kernel

theorem checked_48512 : Scan.checkChunk context facts instructions 48512 128 = true := by
  decide +kernel

theorem checked_48640 : Scan.checkChunk context facts instructions 48640 128 = true := by
  decide +kernel

theorem checked_48768 : Scan.checkChunk context facts instructions 48768 128 = true := by
  decide +kernel

theorem checked_48896 : Scan.checkChunk context facts instructions 48896 128 = true := by
  decide +kernel

theorem checked_49024 : Scan.checkChunk context facts instructions 49024 128 = true := by
  decide +kernel

theorem holds_49152 (hr : ∀ r : Fin 4, eval subgroupGenerator (extraRelatorWord r) = 1) :
    ∀ n, n < 49152 → Holds smallSubgroup subgroupGenerator (definitions.repr subgroupGenerator) (facts n) := by
  have h45184 := Scan.chunk_sound (context_valid hr) facts instructions
    45056 128 (holds_45056 hr) checked_45056
  have h45312 := Scan.chunk_sound (context_valid hr) facts instructions
    45184 128 h45184 checked_45184
  have h45440 := Scan.chunk_sound (context_valid hr) facts instructions
    45312 128 h45312 checked_45312
  have h45568 := Scan.chunk_sound (context_valid hr) facts instructions
    45440 128 h45440 checked_45440
  have h45696 := Scan.chunk_sound (context_valid hr) facts instructions
    45568 128 h45568 checked_45568
  have h45824 := Scan.chunk_sound (context_valid hr) facts instructions
    45696 128 h45696 checked_45696
  have h45952 := Scan.chunk_sound (context_valid hr) facts instructions
    45824 128 h45824 checked_45824
  have h46080 := Scan.chunk_sound (context_valid hr) facts instructions
    45952 128 h45952 checked_45952
  have h46208 := Scan.chunk_sound (context_valid hr) facts instructions
    46080 128 h46080 checked_46080
  have h46336 := Scan.chunk_sound (context_valid hr) facts instructions
    46208 128 h46208 checked_46208
  have h46464 := Scan.chunk_sound (context_valid hr) facts instructions
    46336 128 h46336 checked_46336
  have h46592 := Scan.chunk_sound (context_valid hr) facts instructions
    46464 128 h46464 checked_46464
  have h46720 := Scan.chunk_sound (context_valid hr) facts instructions
    46592 128 h46592 checked_46592
  have h46848 := Scan.chunk_sound (context_valid hr) facts instructions
    46720 128 h46720 checked_46720
  have h46976 := Scan.chunk_sound (context_valid hr) facts instructions
    46848 128 h46848 checked_46848
  have h47104 := Scan.chunk_sound (context_valid hr) facts instructions
    46976 128 h46976 checked_46976
  have h47232 := Scan.chunk_sound (context_valid hr) facts instructions
    47104 128 h47104 checked_47104
  have h47360 := Scan.chunk_sound (context_valid hr) facts instructions
    47232 128 h47232 checked_47232
  have h47488 := Scan.chunk_sound (context_valid hr) facts instructions
    47360 128 h47360 checked_47360
  have h47616 := Scan.chunk_sound (context_valid hr) facts instructions
    47488 128 h47488 checked_47488
  have h47744 := Scan.chunk_sound (context_valid hr) facts instructions
    47616 128 h47616 checked_47616
  have h47872 := Scan.chunk_sound (context_valid hr) facts instructions
    47744 128 h47744 checked_47744
  have h48000 := Scan.chunk_sound (context_valid hr) facts instructions
    47872 128 h47872 checked_47872
  have h48128 := Scan.chunk_sound (context_valid hr) facts instructions
    48000 128 h48000 checked_48000
  have h48256 := Scan.chunk_sound (context_valid hr) facts instructions
    48128 128 h48128 checked_48128
  have h48384 := Scan.chunk_sound (context_valid hr) facts instructions
    48256 128 h48256 checked_48256
  have h48512 := Scan.chunk_sound (context_valid hr) facts instructions
    48384 128 h48384 checked_48384
  have h48640 := Scan.chunk_sound (context_valid hr) facts instructions
    48512 128 h48512 checked_48512
  have h48768 := Scan.chunk_sound (context_valid hr) facts instructions
    48640 128 h48640 checked_48640
  have h48896 := Scan.chunk_sound (context_valid hr) facts instructions
    48768 128 h48768 checked_48768
  have h49024 := Scan.chunk_sound (context_valid hr) facts instructions
    48896 128 h48896 checked_48896
  have h49152 := Scan.chunk_sound (context_valid hr) facts instructions
    49024 128 h49024 checked_49024
  exact h49152

end Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced.Bound.LocalFinite.Certificate
