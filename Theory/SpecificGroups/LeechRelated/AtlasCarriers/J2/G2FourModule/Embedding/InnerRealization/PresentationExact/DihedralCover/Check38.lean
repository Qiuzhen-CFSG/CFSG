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
theorem checked_622592 : Scan.checkChunk context facts instructions 622592 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_623104 : Scan.checkChunk context facts instructions 623104 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_623616 : Scan.checkChunk context facts instructions 623616 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_624128 : Scan.checkChunk context facts instructions 624128 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_624640 : Scan.checkChunk context facts instructions 624640 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_625152 : Scan.checkChunk context facts instructions 625152 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_625664 : Scan.checkChunk context facts instructions 625664 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_626176 : Scan.checkChunk context facts instructions 626176 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_626688 : Scan.checkChunk context facts instructions 626688 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_627200 : Scan.checkChunk context facts instructions 627200 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_627712 : Scan.checkChunk context facts instructions 627712 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_628224 : Scan.checkChunk context facts instructions 628224 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_628736 : Scan.checkChunk context facts instructions 628736 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_629248 : Scan.checkChunk context facts instructions 629248 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_629760 : Scan.checkChunk context facts instructions 629760 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_630272 : Scan.checkChunk context facts instructions 630272 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_630784 : Scan.checkChunk context facts instructions 630784 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_631296 : Scan.checkChunk context facts instructions 631296 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_631808 : Scan.checkChunk context facts instructions 631808 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_632320 : Scan.checkChunk context facts instructions 632320 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_632832 : Scan.checkChunk context facts instructions 632832 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_633344 : Scan.checkChunk context facts instructions 633344 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_633856 : Scan.checkChunk context facts instructions 633856 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_634368 : Scan.checkChunk context facts instructions 634368 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_634880 : Scan.checkChunk context facts instructions 634880 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_635392 : Scan.checkChunk context facts instructions 635392 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_635904 : Scan.checkChunk context facts instructions 635904 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_636416 : Scan.checkChunk context facts instructions 636416 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_636928 : Scan.checkChunk context facts instructions 636928 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_637440 : Scan.checkChunk context facts instructions 637440 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_637952 : Scan.checkChunk context facts instructions 637952 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_638464 : Scan.checkChunk context facts instructions 638464 512 = true := by
  decide +kernel

theorem sound_622592 (prior : ∀ n, n < 622592 →
    Holds dihedral generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 638976 → Holds dihedral generator (definitions.repr generator) (facts n) := by
  have h623104 := Scan.chunk_sound context_valid facts instructions 622592 512
    prior checked_622592
  have h623616 := Scan.chunk_sound context_valid facts instructions 623104 512
    h623104 checked_623104
  have h624128 := Scan.chunk_sound context_valid facts instructions 623616 512
    h623616 checked_623616
  have h624640 := Scan.chunk_sound context_valid facts instructions 624128 512
    h624128 checked_624128
  have h625152 := Scan.chunk_sound context_valid facts instructions 624640 512
    h624640 checked_624640
  have h625664 := Scan.chunk_sound context_valid facts instructions 625152 512
    h625152 checked_625152
  have h626176 := Scan.chunk_sound context_valid facts instructions 625664 512
    h625664 checked_625664
  have h626688 := Scan.chunk_sound context_valid facts instructions 626176 512
    h626176 checked_626176
  have h627200 := Scan.chunk_sound context_valid facts instructions 626688 512
    h626688 checked_626688
  have h627712 := Scan.chunk_sound context_valid facts instructions 627200 512
    h627200 checked_627200
  have h628224 := Scan.chunk_sound context_valid facts instructions 627712 512
    h627712 checked_627712
  have h628736 := Scan.chunk_sound context_valid facts instructions 628224 512
    h628224 checked_628224
  have h629248 := Scan.chunk_sound context_valid facts instructions 628736 512
    h628736 checked_628736
  have h629760 := Scan.chunk_sound context_valid facts instructions 629248 512
    h629248 checked_629248
  have h630272 := Scan.chunk_sound context_valid facts instructions 629760 512
    h629760 checked_629760
  have h630784 := Scan.chunk_sound context_valid facts instructions 630272 512
    h630272 checked_630272
  have h631296 := Scan.chunk_sound context_valid facts instructions 630784 512
    h630784 checked_630784
  have h631808 := Scan.chunk_sound context_valid facts instructions 631296 512
    h631296 checked_631296
  have h632320 := Scan.chunk_sound context_valid facts instructions 631808 512
    h631808 checked_631808
  have h632832 := Scan.chunk_sound context_valid facts instructions 632320 512
    h632320 checked_632320
  have h633344 := Scan.chunk_sound context_valid facts instructions 632832 512
    h632832 checked_632832
  have h633856 := Scan.chunk_sound context_valid facts instructions 633344 512
    h633344 checked_633344
  have h634368 := Scan.chunk_sound context_valid facts instructions 633856 512
    h633856 checked_633856
  have h634880 := Scan.chunk_sound context_valid facts instructions 634368 512
    h634368 checked_634368
  have h635392 := Scan.chunk_sound context_valid facts instructions 634880 512
    h634880 checked_634880
  have h635904 := Scan.chunk_sound context_valid facts instructions 635392 512
    h635392 checked_635392
  have h636416 := Scan.chunk_sound context_valid facts instructions 635904 512
    h635904 checked_635904
  have h636928 := Scan.chunk_sound context_valid facts instructions 636416 512
    h636416 checked_636416
  have h637440 := Scan.chunk_sound context_valid facts instructions 636928 512
    h636928 checked_636928
  have h637952 := Scan.chunk_sound context_valid facts instructions 637440 512
    h637440 checked_637440
  have h638464 := Scan.chunk_sound context_valid facts instructions 637952 512
    h637952 checked_637952
  have h638976 := Scan.chunk_sound context_valid facts instructions 638464 512
    h638464 checked_638464
  exact h638976

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCertificate
