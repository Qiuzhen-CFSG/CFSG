module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCover.Tables

/-! Kernel checks for the literal ATLAS J2G1-P2 dihedral coset certificate.
Each retained deduction is checked against earlier facts and proved relator loops.
Sequential declarations bound the reduction cache. See `source/README.md`. -/

public section
namespace Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCertificate
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 4096 in
theorem checked_278528 : Scan.checkChunk context facts instructions 278528 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_279040 : Scan.checkChunk context facts instructions 279040 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_279552 : Scan.checkChunk context facts instructions 279552 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_280064 : Scan.checkChunk context facts instructions 280064 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_280576 : Scan.checkChunk context facts instructions 280576 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_281088 : Scan.checkChunk context facts instructions 281088 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_281600 : Scan.checkChunk context facts instructions 281600 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_282112 : Scan.checkChunk context facts instructions 282112 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_282624 : Scan.checkChunk context facts instructions 282624 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_283136 : Scan.checkChunk context facts instructions 283136 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_283648 : Scan.checkChunk context facts instructions 283648 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_284160 : Scan.checkChunk context facts instructions 284160 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_284672 : Scan.checkChunk context facts instructions 284672 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_285184 : Scan.checkChunk context facts instructions 285184 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_285696 : Scan.checkChunk context facts instructions 285696 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_286208 : Scan.checkChunk context facts instructions 286208 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_286720 : Scan.checkChunk context facts instructions 286720 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_287232 : Scan.checkChunk context facts instructions 287232 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_287744 : Scan.checkChunk context facts instructions 287744 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_288256 : Scan.checkChunk context facts instructions 288256 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_288768 : Scan.checkChunk context facts instructions 288768 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_289280 : Scan.checkChunk context facts instructions 289280 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_289792 : Scan.checkChunk context facts instructions 289792 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_290304 : Scan.checkChunk context facts instructions 290304 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_290816 : Scan.checkChunk context facts instructions 290816 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_291328 : Scan.checkChunk context facts instructions 291328 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_291840 : Scan.checkChunk context facts instructions 291840 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_292352 : Scan.checkChunk context facts instructions 292352 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_292864 : Scan.checkChunk context facts instructions 292864 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_293376 : Scan.checkChunk context facts instructions 293376 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_293888 : Scan.checkChunk context facts instructions 293888 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_294400 : Scan.checkChunk context facts instructions 294400 512 = true := by
  decide +kernel

theorem sound_278528 (prior : ∀ n, n < 278528 →
    Holds dihedral generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 294912 → Holds dihedral generator (definitions.repr generator) (facts n) := by
  have h279040 := Scan.chunk_sound context_valid facts instructions 278528 512
    prior checked_278528
  have h279552 := Scan.chunk_sound context_valid facts instructions 279040 512
    h279040 checked_279040
  have h280064 := Scan.chunk_sound context_valid facts instructions 279552 512
    h279552 checked_279552
  have h280576 := Scan.chunk_sound context_valid facts instructions 280064 512
    h280064 checked_280064
  have h281088 := Scan.chunk_sound context_valid facts instructions 280576 512
    h280576 checked_280576
  have h281600 := Scan.chunk_sound context_valid facts instructions 281088 512
    h281088 checked_281088
  have h282112 := Scan.chunk_sound context_valid facts instructions 281600 512
    h281600 checked_281600
  have h282624 := Scan.chunk_sound context_valid facts instructions 282112 512
    h282112 checked_282112
  have h283136 := Scan.chunk_sound context_valid facts instructions 282624 512
    h282624 checked_282624
  have h283648 := Scan.chunk_sound context_valid facts instructions 283136 512
    h283136 checked_283136
  have h284160 := Scan.chunk_sound context_valid facts instructions 283648 512
    h283648 checked_283648
  have h284672 := Scan.chunk_sound context_valid facts instructions 284160 512
    h284160 checked_284160
  have h285184 := Scan.chunk_sound context_valid facts instructions 284672 512
    h284672 checked_284672
  have h285696 := Scan.chunk_sound context_valid facts instructions 285184 512
    h285184 checked_285184
  have h286208 := Scan.chunk_sound context_valid facts instructions 285696 512
    h285696 checked_285696
  have h286720 := Scan.chunk_sound context_valid facts instructions 286208 512
    h286208 checked_286208
  have h287232 := Scan.chunk_sound context_valid facts instructions 286720 512
    h286720 checked_286720
  have h287744 := Scan.chunk_sound context_valid facts instructions 287232 512
    h287232 checked_287232
  have h288256 := Scan.chunk_sound context_valid facts instructions 287744 512
    h287744 checked_287744
  have h288768 := Scan.chunk_sound context_valid facts instructions 288256 512
    h288256 checked_288256
  have h289280 := Scan.chunk_sound context_valid facts instructions 288768 512
    h288768 checked_288768
  have h289792 := Scan.chunk_sound context_valid facts instructions 289280 512
    h289280 checked_289280
  have h290304 := Scan.chunk_sound context_valid facts instructions 289792 512
    h289792 checked_289792
  have h290816 := Scan.chunk_sound context_valid facts instructions 290304 512
    h290304 checked_290304
  have h291328 := Scan.chunk_sound context_valid facts instructions 290816 512
    h290816 checked_290816
  have h291840 := Scan.chunk_sound context_valid facts instructions 291328 512
    h291328 checked_291328
  have h292352 := Scan.chunk_sound context_valid facts instructions 291840 512
    h291840 checked_291840
  have h292864 := Scan.chunk_sound context_valid facts instructions 292352 512
    h292352 checked_292352
  have h293376 := Scan.chunk_sound context_valid facts instructions 292864 512
    h292864 checked_292864
  have h293888 := Scan.chunk_sound context_valid facts instructions 293376 512
    h293376 checked_293376
  have h294400 := Scan.chunk_sound context_valid facts instructions 293888 512
    h293888 checked_293888
  have h294912 := Scan.chunk_sound context_valid facts instructions 294400 512
    h294400 checked_294400
  exact h294912

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCertificate
