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
theorem checked_491520 : Scan.checkChunk context facts instructions 491520 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_492032 : Scan.checkChunk context facts instructions 492032 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_492544 : Scan.checkChunk context facts instructions 492544 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_493056 : Scan.checkChunk context facts instructions 493056 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_493568 : Scan.checkChunk context facts instructions 493568 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_494080 : Scan.checkChunk context facts instructions 494080 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_494592 : Scan.checkChunk context facts instructions 494592 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_495104 : Scan.checkChunk context facts instructions 495104 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_495616 : Scan.checkChunk context facts instructions 495616 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_496128 : Scan.checkChunk context facts instructions 496128 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_496640 : Scan.checkChunk context facts instructions 496640 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_497152 : Scan.checkChunk context facts instructions 497152 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_497664 : Scan.checkChunk context facts instructions 497664 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_498176 : Scan.checkChunk context facts instructions 498176 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_498688 : Scan.checkChunk context facts instructions 498688 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_499200 : Scan.checkChunk context facts instructions 499200 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_499712 : Scan.checkChunk context facts instructions 499712 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_500224 : Scan.checkChunk context facts instructions 500224 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_500736 : Scan.checkChunk context facts instructions 500736 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_501248 : Scan.checkChunk context facts instructions 501248 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_501760 : Scan.checkChunk context facts instructions 501760 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_502272 : Scan.checkChunk context facts instructions 502272 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_502784 : Scan.checkChunk context facts instructions 502784 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_503296 : Scan.checkChunk context facts instructions 503296 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_503808 : Scan.checkChunk context facts instructions 503808 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_504320 : Scan.checkChunk context facts instructions 504320 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_504832 : Scan.checkChunk context facts instructions 504832 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_505344 : Scan.checkChunk context facts instructions 505344 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_505856 : Scan.checkChunk context facts instructions 505856 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_506368 : Scan.checkChunk context facts instructions 506368 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_506880 : Scan.checkChunk context facts instructions 506880 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_507392 : Scan.checkChunk context facts instructions 507392 512 = true := by
  decide +kernel

theorem sound_491520 (prior : ∀ n, n < 491520 →
    Holds dihedral generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 507904 → Holds dihedral generator (definitions.repr generator) (facts n) := by
  have h492032 := Scan.chunk_sound context_valid facts instructions 491520 512
    prior checked_491520
  have h492544 := Scan.chunk_sound context_valid facts instructions 492032 512
    h492032 checked_492032
  have h493056 := Scan.chunk_sound context_valid facts instructions 492544 512
    h492544 checked_492544
  have h493568 := Scan.chunk_sound context_valid facts instructions 493056 512
    h493056 checked_493056
  have h494080 := Scan.chunk_sound context_valid facts instructions 493568 512
    h493568 checked_493568
  have h494592 := Scan.chunk_sound context_valid facts instructions 494080 512
    h494080 checked_494080
  have h495104 := Scan.chunk_sound context_valid facts instructions 494592 512
    h494592 checked_494592
  have h495616 := Scan.chunk_sound context_valid facts instructions 495104 512
    h495104 checked_495104
  have h496128 := Scan.chunk_sound context_valid facts instructions 495616 512
    h495616 checked_495616
  have h496640 := Scan.chunk_sound context_valid facts instructions 496128 512
    h496128 checked_496128
  have h497152 := Scan.chunk_sound context_valid facts instructions 496640 512
    h496640 checked_496640
  have h497664 := Scan.chunk_sound context_valid facts instructions 497152 512
    h497152 checked_497152
  have h498176 := Scan.chunk_sound context_valid facts instructions 497664 512
    h497664 checked_497664
  have h498688 := Scan.chunk_sound context_valid facts instructions 498176 512
    h498176 checked_498176
  have h499200 := Scan.chunk_sound context_valid facts instructions 498688 512
    h498688 checked_498688
  have h499712 := Scan.chunk_sound context_valid facts instructions 499200 512
    h499200 checked_499200
  have h500224 := Scan.chunk_sound context_valid facts instructions 499712 512
    h499712 checked_499712
  have h500736 := Scan.chunk_sound context_valid facts instructions 500224 512
    h500224 checked_500224
  have h501248 := Scan.chunk_sound context_valid facts instructions 500736 512
    h500736 checked_500736
  have h501760 := Scan.chunk_sound context_valid facts instructions 501248 512
    h501248 checked_501248
  have h502272 := Scan.chunk_sound context_valid facts instructions 501760 512
    h501760 checked_501760
  have h502784 := Scan.chunk_sound context_valid facts instructions 502272 512
    h502272 checked_502272
  have h503296 := Scan.chunk_sound context_valid facts instructions 502784 512
    h502784 checked_502784
  have h503808 := Scan.chunk_sound context_valid facts instructions 503296 512
    h503296 checked_503296
  have h504320 := Scan.chunk_sound context_valid facts instructions 503808 512
    h503808 checked_503808
  have h504832 := Scan.chunk_sound context_valid facts instructions 504320 512
    h504320 checked_504320
  have h505344 := Scan.chunk_sound context_valid facts instructions 504832 512
    h504832 checked_504832
  have h505856 := Scan.chunk_sound context_valid facts instructions 505344 512
    h505344 checked_505344
  have h506368 := Scan.chunk_sound context_valid facts instructions 505856 512
    h505856 checked_505856
  have h506880 := Scan.chunk_sound context_valid facts instructions 506368 512
    h506368 checked_506368
  have h507392 := Scan.chunk_sound context_valid facts instructions 506880 512
    h506880 checked_506880
  have h507904 := Scan.chunk_sound context_valid facts instructions 507392 512
    h507392 checked_507392
  exact h507904

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCertificate
