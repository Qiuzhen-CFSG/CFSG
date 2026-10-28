module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.M1aBound.FiniteBound.Reduced.Bound.LocalFinite.Checks12

/-! Kernel checks for the conditional local coset certificate.
Each accepted step is an actual word deduction. The four relator identities
remain explicit premises; see `source/README.md`. -/

@[expose] public section
namespace Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced.Bound.LocalFinite.Certificate
open Subgroup.CosetWordCertificate

theorem checked_53248 : Scan.checkChunk context facts instructions 53248 128 = true := by
  decide +kernel

theorem checked_53376 : Scan.checkChunk context facts instructions 53376 128 = true := by
  decide +kernel

theorem checked_53504 : Scan.checkChunk context facts instructions 53504 128 = true := by
  decide +kernel

theorem checked_53632 : Scan.checkChunk context facts instructions 53632 128 = true := by
  decide +kernel

theorem checked_53760 : Scan.checkChunk context facts instructions 53760 128 = true := by
  decide +kernel

theorem checked_53888 : Scan.checkChunk context facts instructions 53888 128 = true := by
  decide +kernel

theorem checked_54016 : Scan.checkChunk context facts instructions 54016 128 = true := by
  decide +kernel

theorem checked_54144 : Scan.checkChunk context facts instructions 54144 77 = true := by
  decide +kernel

theorem holds_54221 (hr : ∀ r : Fin 4, eval subgroupGenerator (extraRelatorWord r) = 1) :
    ∀ n, n < 54221 → Holds smallSubgroup subgroupGenerator (definitions.repr subgroupGenerator) (facts n) := by
  have h53376 := Scan.chunk_sound (context_valid hr) facts instructions
    53248 128 (holds_53248 hr) checked_53248
  have h53504 := Scan.chunk_sound (context_valid hr) facts instructions
    53376 128 h53376 checked_53376
  have h53632 := Scan.chunk_sound (context_valid hr) facts instructions
    53504 128 h53504 checked_53504
  have h53760 := Scan.chunk_sound (context_valid hr) facts instructions
    53632 128 h53632 checked_53632
  have h53888 := Scan.chunk_sound (context_valid hr) facts instructions
    53760 128 h53760 checked_53760
  have h54016 := Scan.chunk_sound (context_valid hr) facts instructions
    53888 128 h53888 checked_53888
  have h54144 := Scan.chunk_sound (context_valid hr) facts instructions
    54016 128 h54016 checked_54016
  have h54221 := Scan.chunk_sound (context_valid hr) facts instructions
    54144 77 h54144 checked_54144
  exact h54221

end Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced.Bound.LocalFinite.Certificate
