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
theorem checked_606208 : Scan.checkChunk context facts instructions 606208 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_606720 : Scan.checkChunk context facts instructions 606720 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_607232 : Scan.checkChunk context facts instructions 607232 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_607744 : Scan.checkChunk context facts instructions 607744 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_608256 : Scan.checkChunk context facts instructions 608256 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_608768 : Scan.checkChunk context facts instructions 608768 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_609280 : Scan.checkChunk context facts instructions 609280 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_609792 : Scan.checkChunk context facts instructions 609792 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_610304 : Scan.checkChunk context facts instructions 610304 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_610816 : Scan.checkChunk context facts instructions 610816 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_611328 : Scan.checkChunk context facts instructions 611328 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_611840 : Scan.checkChunk context facts instructions 611840 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_612352 : Scan.checkChunk context facts instructions 612352 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_612864 : Scan.checkChunk context facts instructions 612864 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_613376 : Scan.checkChunk context facts instructions 613376 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_613888 : Scan.checkChunk context facts instructions 613888 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_614400 : Scan.checkChunk context facts instructions 614400 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_614912 : Scan.checkChunk context facts instructions 614912 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_615424 : Scan.checkChunk context facts instructions 615424 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_615936 : Scan.checkChunk context facts instructions 615936 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_616448 : Scan.checkChunk context facts instructions 616448 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_616960 : Scan.checkChunk context facts instructions 616960 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_617472 : Scan.checkChunk context facts instructions 617472 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_617984 : Scan.checkChunk context facts instructions 617984 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_618496 : Scan.checkChunk context facts instructions 618496 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_619008 : Scan.checkChunk context facts instructions 619008 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_619520 : Scan.checkChunk context facts instructions 619520 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_620032 : Scan.checkChunk context facts instructions 620032 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_620544 : Scan.checkChunk context facts instructions 620544 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_621056 : Scan.checkChunk context facts instructions 621056 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_621568 : Scan.checkChunk context facts instructions 621568 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_622080 : Scan.checkChunk context facts instructions 622080 512 = true := by
  decide +kernel

theorem sound_606208 (prior : ∀ n, n < 606208 →
    Holds dihedral generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 622592 → Holds dihedral generator (definitions.repr generator) (facts n) := by
  have h606720 := Scan.chunk_sound context_valid facts instructions 606208 512
    prior checked_606208
  have h607232 := Scan.chunk_sound context_valid facts instructions 606720 512
    h606720 checked_606720
  have h607744 := Scan.chunk_sound context_valid facts instructions 607232 512
    h607232 checked_607232
  have h608256 := Scan.chunk_sound context_valid facts instructions 607744 512
    h607744 checked_607744
  have h608768 := Scan.chunk_sound context_valid facts instructions 608256 512
    h608256 checked_608256
  have h609280 := Scan.chunk_sound context_valid facts instructions 608768 512
    h608768 checked_608768
  have h609792 := Scan.chunk_sound context_valid facts instructions 609280 512
    h609280 checked_609280
  have h610304 := Scan.chunk_sound context_valid facts instructions 609792 512
    h609792 checked_609792
  have h610816 := Scan.chunk_sound context_valid facts instructions 610304 512
    h610304 checked_610304
  have h611328 := Scan.chunk_sound context_valid facts instructions 610816 512
    h610816 checked_610816
  have h611840 := Scan.chunk_sound context_valid facts instructions 611328 512
    h611328 checked_611328
  have h612352 := Scan.chunk_sound context_valid facts instructions 611840 512
    h611840 checked_611840
  have h612864 := Scan.chunk_sound context_valid facts instructions 612352 512
    h612352 checked_612352
  have h613376 := Scan.chunk_sound context_valid facts instructions 612864 512
    h612864 checked_612864
  have h613888 := Scan.chunk_sound context_valid facts instructions 613376 512
    h613376 checked_613376
  have h614400 := Scan.chunk_sound context_valid facts instructions 613888 512
    h613888 checked_613888
  have h614912 := Scan.chunk_sound context_valid facts instructions 614400 512
    h614400 checked_614400
  have h615424 := Scan.chunk_sound context_valid facts instructions 614912 512
    h614912 checked_614912
  have h615936 := Scan.chunk_sound context_valid facts instructions 615424 512
    h615424 checked_615424
  have h616448 := Scan.chunk_sound context_valid facts instructions 615936 512
    h615936 checked_615936
  have h616960 := Scan.chunk_sound context_valid facts instructions 616448 512
    h616448 checked_616448
  have h617472 := Scan.chunk_sound context_valid facts instructions 616960 512
    h616960 checked_616960
  have h617984 := Scan.chunk_sound context_valid facts instructions 617472 512
    h617472 checked_617472
  have h618496 := Scan.chunk_sound context_valid facts instructions 617984 512
    h617984 checked_617984
  have h619008 := Scan.chunk_sound context_valid facts instructions 618496 512
    h618496 checked_618496
  have h619520 := Scan.chunk_sound context_valid facts instructions 619008 512
    h619008 checked_619008
  have h620032 := Scan.chunk_sound context_valid facts instructions 619520 512
    h619520 checked_619520
  have h620544 := Scan.chunk_sound context_valid facts instructions 620032 512
    h620032 checked_620032
  have h621056 := Scan.chunk_sound context_valid facts instructions 620544 512
    h620544 checked_620544
  have h621568 := Scan.chunk_sound context_valid facts instructions 621056 512
    h621056 checked_621056
  have h622080 := Scan.chunk_sound context_valid facts instructions 621568 512
    h621568 checked_621568
  have h622592 := Scan.chunk_sound context_valid facts instructions 622080 512
    h622080 checked_622080
  exact h622592

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCertificate
