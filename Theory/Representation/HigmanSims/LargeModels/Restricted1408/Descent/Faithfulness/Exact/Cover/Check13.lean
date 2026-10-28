module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.Tables

/-! Centralizer-coset certificate for the thirteen ATLAS HS relators.
Untrusted data generated from the retained trace; all deduction checks use
Lean's kernel and the actual abstract relations. See `source/README.md`. -/

public section
namespace Sporadic.LeechRelated.HS.AtlasPresentation.Exact.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 4096 in
theorem checked_212992 : Scan.checkChunk context facts instructions 212992 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_213504 : Scan.checkChunk context facts instructions 213504 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_214016 : Scan.checkChunk context facts instructions 214016 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_214528 : Scan.checkChunk context facts instructions 214528 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_215040 : Scan.checkChunk context facts instructions 215040 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_215552 : Scan.checkChunk context facts instructions 215552 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_216064 : Scan.checkChunk context facts instructions 216064 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_216576 : Scan.checkChunk context facts instructions 216576 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_217088 : Scan.checkChunk context facts instructions 217088 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_217600 : Scan.checkChunk context facts instructions 217600 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_218112 : Scan.checkChunk context facts instructions 218112 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_218624 : Scan.checkChunk context facts instructions 218624 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_219136 : Scan.checkChunk context facts instructions 219136 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_219648 : Scan.checkChunk context facts instructions 219648 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_220160 : Scan.checkChunk context facts instructions 220160 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_220672 : Scan.checkChunk context facts instructions 220672 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_221184 : Scan.checkChunk context facts instructions 221184 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_221696 : Scan.checkChunk context facts instructions 221696 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_222208 : Scan.checkChunk context facts instructions 222208 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_222720 : Scan.checkChunk context facts instructions 222720 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_223232 : Scan.checkChunk context facts instructions 223232 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_223744 : Scan.checkChunk context facts instructions 223744 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_224256 : Scan.checkChunk context facts instructions 224256 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_224768 : Scan.checkChunk context facts instructions 224768 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_225280 : Scan.checkChunk context facts instructions 225280 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_225792 : Scan.checkChunk context facts instructions 225792 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_226304 : Scan.checkChunk context facts instructions 226304 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_226816 : Scan.checkChunk context facts instructions 226816 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_227328 : Scan.checkChunk context facts instructions 227328 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_227840 : Scan.checkChunk context facts instructions 227840 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_228352 : Scan.checkChunk context facts instructions 228352 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_228864 : Scan.checkChunk context facts instructions 228864 512 = true := by
  decide +kernel

theorem all_hold_229376 (prior : ∀ n, n < 212992 → Holds centralizer certGenerator (definitions.repr certGenerator) (facts n)) : ∀ n, n < 229376 →
    Holds centralizer certGenerator (definitions.repr certGenerator) (facts n) := by
  have h213504 := Scan.chunk_sound context_valid facts instructions 212992 512
    prior checked_212992
  have h214016 := Scan.chunk_sound context_valid facts instructions 213504 512
    h213504 checked_213504
  have h214528 := Scan.chunk_sound context_valid facts instructions 214016 512
    h214016 checked_214016
  have h215040 := Scan.chunk_sound context_valid facts instructions 214528 512
    h214528 checked_214528
  have h215552 := Scan.chunk_sound context_valid facts instructions 215040 512
    h215040 checked_215040
  have h216064 := Scan.chunk_sound context_valid facts instructions 215552 512
    h215552 checked_215552
  have h216576 := Scan.chunk_sound context_valid facts instructions 216064 512
    h216064 checked_216064
  have h217088 := Scan.chunk_sound context_valid facts instructions 216576 512
    h216576 checked_216576
  have h217600 := Scan.chunk_sound context_valid facts instructions 217088 512
    h217088 checked_217088
  have h218112 := Scan.chunk_sound context_valid facts instructions 217600 512
    h217600 checked_217600
  have h218624 := Scan.chunk_sound context_valid facts instructions 218112 512
    h218112 checked_218112
  have h219136 := Scan.chunk_sound context_valid facts instructions 218624 512
    h218624 checked_218624
  have h219648 := Scan.chunk_sound context_valid facts instructions 219136 512
    h219136 checked_219136
  have h220160 := Scan.chunk_sound context_valid facts instructions 219648 512
    h219648 checked_219648
  have h220672 := Scan.chunk_sound context_valid facts instructions 220160 512
    h220160 checked_220160
  have h221184 := Scan.chunk_sound context_valid facts instructions 220672 512
    h220672 checked_220672
  have h221696 := Scan.chunk_sound context_valid facts instructions 221184 512
    h221184 checked_221184
  have h222208 := Scan.chunk_sound context_valid facts instructions 221696 512
    h221696 checked_221696
  have h222720 := Scan.chunk_sound context_valid facts instructions 222208 512
    h222208 checked_222208
  have h223232 := Scan.chunk_sound context_valid facts instructions 222720 512
    h222720 checked_222720
  have h223744 := Scan.chunk_sound context_valid facts instructions 223232 512
    h223232 checked_223232
  have h224256 := Scan.chunk_sound context_valid facts instructions 223744 512
    h223744 checked_223744
  have h224768 := Scan.chunk_sound context_valid facts instructions 224256 512
    h224256 checked_224256
  have h225280 := Scan.chunk_sound context_valid facts instructions 224768 512
    h224768 checked_224768
  have h225792 := Scan.chunk_sound context_valid facts instructions 225280 512
    h225280 checked_225280
  have h226304 := Scan.chunk_sound context_valid facts instructions 225792 512
    h225792 checked_225792
  have h226816 := Scan.chunk_sound context_valid facts instructions 226304 512
    h226304 checked_226304
  have h227328 := Scan.chunk_sound context_valid facts instructions 226816 512
    h226816 checked_226816
  have h227840 := Scan.chunk_sound context_valid facts instructions 227328 512
    h227328 checked_227328
  have h228352 := Scan.chunk_sound context_valid facts instructions 227840 512
    h227840 checked_227840
  have h228864 := Scan.chunk_sound context_valid facts instructions 228352 512
    h228352 checked_228352
  have h229376 := Scan.chunk_sound context_valid facts instructions 228864 512
    h228864 checked_228864
  exact h229376

end Sporadic.LeechRelated.HS.AtlasPresentation.Exact.Cover
