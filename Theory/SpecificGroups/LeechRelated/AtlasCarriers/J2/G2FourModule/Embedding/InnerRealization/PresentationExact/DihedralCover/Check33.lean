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
theorem checked_540672 : Scan.checkChunk context facts instructions 540672 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_541184 : Scan.checkChunk context facts instructions 541184 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_541696 : Scan.checkChunk context facts instructions 541696 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_542208 : Scan.checkChunk context facts instructions 542208 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_542720 : Scan.checkChunk context facts instructions 542720 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_543232 : Scan.checkChunk context facts instructions 543232 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_543744 : Scan.checkChunk context facts instructions 543744 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_544256 : Scan.checkChunk context facts instructions 544256 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_544768 : Scan.checkChunk context facts instructions 544768 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_545280 : Scan.checkChunk context facts instructions 545280 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_545792 : Scan.checkChunk context facts instructions 545792 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_546304 : Scan.checkChunk context facts instructions 546304 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_546816 : Scan.checkChunk context facts instructions 546816 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_547328 : Scan.checkChunk context facts instructions 547328 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_547840 : Scan.checkChunk context facts instructions 547840 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_548352 : Scan.checkChunk context facts instructions 548352 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_548864 : Scan.checkChunk context facts instructions 548864 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_549376 : Scan.checkChunk context facts instructions 549376 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_549888 : Scan.checkChunk context facts instructions 549888 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_550400 : Scan.checkChunk context facts instructions 550400 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_550912 : Scan.checkChunk context facts instructions 550912 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_551424 : Scan.checkChunk context facts instructions 551424 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_551936 : Scan.checkChunk context facts instructions 551936 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_552448 : Scan.checkChunk context facts instructions 552448 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_552960 : Scan.checkChunk context facts instructions 552960 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_553472 : Scan.checkChunk context facts instructions 553472 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_553984 : Scan.checkChunk context facts instructions 553984 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_554496 : Scan.checkChunk context facts instructions 554496 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_555008 : Scan.checkChunk context facts instructions 555008 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_555520 : Scan.checkChunk context facts instructions 555520 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_556032 : Scan.checkChunk context facts instructions 556032 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_556544 : Scan.checkChunk context facts instructions 556544 512 = true := by
  decide +kernel

theorem sound_540672 (prior : ∀ n, n < 540672 →
    Holds dihedral generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 557056 → Holds dihedral generator (definitions.repr generator) (facts n) := by
  have h541184 := Scan.chunk_sound context_valid facts instructions 540672 512
    prior checked_540672
  have h541696 := Scan.chunk_sound context_valid facts instructions 541184 512
    h541184 checked_541184
  have h542208 := Scan.chunk_sound context_valid facts instructions 541696 512
    h541696 checked_541696
  have h542720 := Scan.chunk_sound context_valid facts instructions 542208 512
    h542208 checked_542208
  have h543232 := Scan.chunk_sound context_valid facts instructions 542720 512
    h542720 checked_542720
  have h543744 := Scan.chunk_sound context_valid facts instructions 543232 512
    h543232 checked_543232
  have h544256 := Scan.chunk_sound context_valid facts instructions 543744 512
    h543744 checked_543744
  have h544768 := Scan.chunk_sound context_valid facts instructions 544256 512
    h544256 checked_544256
  have h545280 := Scan.chunk_sound context_valid facts instructions 544768 512
    h544768 checked_544768
  have h545792 := Scan.chunk_sound context_valid facts instructions 545280 512
    h545280 checked_545280
  have h546304 := Scan.chunk_sound context_valid facts instructions 545792 512
    h545792 checked_545792
  have h546816 := Scan.chunk_sound context_valid facts instructions 546304 512
    h546304 checked_546304
  have h547328 := Scan.chunk_sound context_valid facts instructions 546816 512
    h546816 checked_546816
  have h547840 := Scan.chunk_sound context_valid facts instructions 547328 512
    h547328 checked_547328
  have h548352 := Scan.chunk_sound context_valid facts instructions 547840 512
    h547840 checked_547840
  have h548864 := Scan.chunk_sound context_valid facts instructions 548352 512
    h548352 checked_548352
  have h549376 := Scan.chunk_sound context_valid facts instructions 548864 512
    h548864 checked_548864
  have h549888 := Scan.chunk_sound context_valid facts instructions 549376 512
    h549376 checked_549376
  have h550400 := Scan.chunk_sound context_valid facts instructions 549888 512
    h549888 checked_549888
  have h550912 := Scan.chunk_sound context_valid facts instructions 550400 512
    h550400 checked_550400
  have h551424 := Scan.chunk_sound context_valid facts instructions 550912 512
    h550912 checked_550912
  have h551936 := Scan.chunk_sound context_valid facts instructions 551424 512
    h551424 checked_551424
  have h552448 := Scan.chunk_sound context_valid facts instructions 551936 512
    h551936 checked_551936
  have h552960 := Scan.chunk_sound context_valid facts instructions 552448 512
    h552448 checked_552448
  have h553472 := Scan.chunk_sound context_valid facts instructions 552960 512
    h552960 checked_552960
  have h553984 := Scan.chunk_sound context_valid facts instructions 553472 512
    h553472 checked_553472
  have h554496 := Scan.chunk_sound context_valid facts instructions 553984 512
    h553984 checked_553984
  have h555008 := Scan.chunk_sound context_valid facts instructions 554496 512
    h554496 checked_554496
  have h555520 := Scan.chunk_sound context_valid facts instructions 555008 512
    h555008 checked_555008
  have h556032 := Scan.chunk_sound context_valid facts instructions 555520 512
    h555520 checked_555520
  have h556544 := Scan.chunk_sound context_valid facts instructions 556032 512
    h556032 checked_556032
  have h557056 := Scan.chunk_sound context_valid facts instructions 556544 512
    h556544 checked_556544
  exact h557056

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCertificate
