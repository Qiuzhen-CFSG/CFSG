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
theorem checked_98304 : Scan.checkChunk context facts instructions 98304 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_98816 : Scan.checkChunk context facts instructions 98816 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_99328 : Scan.checkChunk context facts instructions 99328 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_99840 : Scan.checkChunk context facts instructions 99840 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_100352 : Scan.checkChunk context facts instructions 100352 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_100864 : Scan.checkChunk context facts instructions 100864 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_101376 : Scan.checkChunk context facts instructions 101376 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_101888 : Scan.checkChunk context facts instructions 101888 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_102400 : Scan.checkChunk context facts instructions 102400 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_102912 : Scan.checkChunk context facts instructions 102912 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_103424 : Scan.checkChunk context facts instructions 103424 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_103936 : Scan.checkChunk context facts instructions 103936 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_104448 : Scan.checkChunk context facts instructions 104448 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_104960 : Scan.checkChunk context facts instructions 104960 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_105472 : Scan.checkChunk context facts instructions 105472 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_105984 : Scan.checkChunk context facts instructions 105984 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_106496 : Scan.checkChunk context facts instructions 106496 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_107008 : Scan.checkChunk context facts instructions 107008 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_107520 : Scan.checkChunk context facts instructions 107520 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_108032 : Scan.checkChunk context facts instructions 108032 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_108544 : Scan.checkChunk context facts instructions 108544 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_109056 : Scan.checkChunk context facts instructions 109056 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_109568 : Scan.checkChunk context facts instructions 109568 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_110080 : Scan.checkChunk context facts instructions 110080 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_110592 : Scan.checkChunk context facts instructions 110592 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_111104 : Scan.checkChunk context facts instructions 111104 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_111616 : Scan.checkChunk context facts instructions 111616 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_112128 : Scan.checkChunk context facts instructions 112128 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_112640 : Scan.checkChunk context facts instructions 112640 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_113152 : Scan.checkChunk context facts instructions 113152 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_113664 : Scan.checkChunk context facts instructions 113664 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_114176 : Scan.checkChunk context facts instructions 114176 512 = true := by
  decide +kernel

theorem sound_98304 (prior : ∀ n, n < 98304 →
    Holds dihedral generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 114688 → Holds dihedral generator (definitions.repr generator) (facts n) := by
  have h98816 := Scan.chunk_sound context_valid facts instructions 98304 512
    prior checked_98304
  have h99328 := Scan.chunk_sound context_valid facts instructions 98816 512
    h98816 checked_98816
  have h99840 := Scan.chunk_sound context_valid facts instructions 99328 512
    h99328 checked_99328
  have h100352 := Scan.chunk_sound context_valid facts instructions 99840 512
    h99840 checked_99840
  have h100864 := Scan.chunk_sound context_valid facts instructions 100352 512
    h100352 checked_100352
  have h101376 := Scan.chunk_sound context_valid facts instructions 100864 512
    h100864 checked_100864
  have h101888 := Scan.chunk_sound context_valid facts instructions 101376 512
    h101376 checked_101376
  have h102400 := Scan.chunk_sound context_valid facts instructions 101888 512
    h101888 checked_101888
  have h102912 := Scan.chunk_sound context_valid facts instructions 102400 512
    h102400 checked_102400
  have h103424 := Scan.chunk_sound context_valid facts instructions 102912 512
    h102912 checked_102912
  have h103936 := Scan.chunk_sound context_valid facts instructions 103424 512
    h103424 checked_103424
  have h104448 := Scan.chunk_sound context_valid facts instructions 103936 512
    h103936 checked_103936
  have h104960 := Scan.chunk_sound context_valid facts instructions 104448 512
    h104448 checked_104448
  have h105472 := Scan.chunk_sound context_valid facts instructions 104960 512
    h104960 checked_104960
  have h105984 := Scan.chunk_sound context_valid facts instructions 105472 512
    h105472 checked_105472
  have h106496 := Scan.chunk_sound context_valid facts instructions 105984 512
    h105984 checked_105984
  have h107008 := Scan.chunk_sound context_valid facts instructions 106496 512
    h106496 checked_106496
  have h107520 := Scan.chunk_sound context_valid facts instructions 107008 512
    h107008 checked_107008
  have h108032 := Scan.chunk_sound context_valid facts instructions 107520 512
    h107520 checked_107520
  have h108544 := Scan.chunk_sound context_valid facts instructions 108032 512
    h108032 checked_108032
  have h109056 := Scan.chunk_sound context_valid facts instructions 108544 512
    h108544 checked_108544
  have h109568 := Scan.chunk_sound context_valid facts instructions 109056 512
    h109056 checked_109056
  have h110080 := Scan.chunk_sound context_valid facts instructions 109568 512
    h109568 checked_109568
  have h110592 := Scan.chunk_sound context_valid facts instructions 110080 512
    h110080 checked_110080
  have h111104 := Scan.chunk_sound context_valid facts instructions 110592 512
    h110592 checked_110592
  have h111616 := Scan.chunk_sound context_valid facts instructions 111104 512
    h111104 checked_111104
  have h112128 := Scan.chunk_sound context_valid facts instructions 111616 512
    h111616 checked_111616
  have h112640 := Scan.chunk_sound context_valid facts instructions 112128 512
    h112128 checked_112128
  have h113152 := Scan.chunk_sound context_valid facts instructions 112640 512
    h112640 checked_112640
  have h113664 := Scan.chunk_sound context_valid facts instructions 113152 512
    h113152 checked_113152
  have h114176 := Scan.chunk_sound context_valid facts instructions 113664 512
    h113664 checked_113664
  have h114688 := Scan.chunk_sound context_valid facts instructions 114176 512
    h114176 checked_114176
  exact h114688

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCertificate
