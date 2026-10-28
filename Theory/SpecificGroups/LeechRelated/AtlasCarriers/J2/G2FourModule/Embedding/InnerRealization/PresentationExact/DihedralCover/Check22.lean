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
theorem checked_360448 : Scan.checkChunk context facts instructions 360448 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_360960 : Scan.checkChunk context facts instructions 360960 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_361472 : Scan.checkChunk context facts instructions 361472 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_361984 : Scan.checkChunk context facts instructions 361984 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_362496 : Scan.checkChunk context facts instructions 362496 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_363008 : Scan.checkChunk context facts instructions 363008 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_363520 : Scan.checkChunk context facts instructions 363520 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_364032 : Scan.checkChunk context facts instructions 364032 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_364544 : Scan.checkChunk context facts instructions 364544 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_365056 : Scan.checkChunk context facts instructions 365056 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_365568 : Scan.checkChunk context facts instructions 365568 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_366080 : Scan.checkChunk context facts instructions 366080 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_366592 : Scan.checkChunk context facts instructions 366592 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_367104 : Scan.checkChunk context facts instructions 367104 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_367616 : Scan.checkChunk context facts instructions 367616 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_368128 : Scan.checkChunk context facts instructions 368128 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_368640 : Scan.checkChunk context facts instructions 368640 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_369152 : Scan.checkChunk context facts instructions 369152 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_369664 : Scan.checkChunk context facts instructions 369664 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_370176 : Scan.checkChunk context facts instructions 370176 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_370688 : Scan.checkChunk context facts instructions 370688 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_371200 : Scan.checkChunk context facts instructions 371200 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_371712 : Scan.checkChunk context facts instructions 371712 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_372224 : Scan.checkChunk context facts instructions 372224 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_372736 : Scan.checkChunk context facts instructions 372736 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_373248 : Scan.checkChunk context facts instructions 373248 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_373760 : Scan.checkChunk context facts instructions 373760 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_374272 : Scan.checkChunk context facts instructions 374272 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_374784 : Scan.checkChunk context facts instructions 374784 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_375296 : Scan.checkChunk context facts instructions 375296 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_375808 : Scan.checkChunk context facts instructions 375808 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_376320 : Scan.checkChunk context facts instructions 376320 512 = true := by
  decide +kernel

theorem sound_360448 (prior : ∀ n, n < 360448 →
    Holds dihedral generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 376832 → Holds dihedral generator (definitions.repr generator) (facts n) := by
  have h360960 := Scan.chunk_sound context_valid facts instructions 360448 512
    prior checked_360448
  have h361472 := Scan.chunk_sound context_valid facts instructions 360960 512
    h360960 checked_360960
  have h361984 := Scan.chunk_sound context_valid facts instructions 361472 512
    h361472 checked_361472
  have h362496 := Scan.chunk_sound context_valid facts instructions 361984 512
    h361984 checked_361984
  have h363008 := Scan.chunk_sound context_valid facts instructions 362496 512
    h362496 checked_362496
  have h363520 := Scan.chunk_sound context_valid facts instructions 363008 512
    h363008 checked_363008
  have h364032 := Scan.chunk_sound context_valid facts instructions 363520 512
    h363520 checked_363520
  have h364544 := Scan.chunk_sound context_valid facts instructions 364032 512
    h364032 checked_364032
  have h365056 := Scan.chunk_sound context_valid facts instructions 364544 512
    h364544 checked_364544
  have h365568 := Scan.chunk_sound context_valid facts instructions 365056 512
    h365056 checked_365056
  have h366080 := Scan.chunk_sound context_valid facts instructions 365568 512
    h365568 checked_365568
  have h366592 := Scan.chunk_sound context_valid facts instructions 366080 512
    h366080 checked_366080
  have h367104 := Scan.chunk_sound context_valid facts instructions 366592 512
    h366592 checked_366592
  have h367616 := Scan.chunk_sound context_valid facts instructions 367104 512
    h367104 checked_367104
  have h368128 := Scan.chunk_sound context_valid facts instructions 367616 512
    h367616 checked_367616
  have h368640 := Scan.chunk_sound context_valid facts instructions 368128 512
    h368128 checked_368128
  have h369152 := Scan.chunk_sound context_valid facts instructions 368640 512
    h368640 checked_368640
  have h369664 := Scan.chunk_sound context_valid facts instructions 369152 512
    h369152 checked_369152
  have h370176 := Scan.chunk_sound context_valid facts instructions 369664 512
    h369664 checked_369664
  have h370688 := Scan.chunk_sound context_valid facts instructions 370176 512
    h370176 checked_370176
  have h371200 := Scan.chunk_sound context_valid facts instructions 370688 512
    h370688 checked_370688
  have h371712 := Scan.chunk_sound context_valid facts instructions 371200 512
    h371200 checked_371200
  have h372224 := Scan.chunk_sound context_valid facts instructions 371712 512
    h371712 checked_371712
  have h372736 := Scan.chunk_sound context_valid facts instructions 372224 512
    h372224 checked_372224
  have h373248 := Scan.chunk_sound context_valid facts instructions 372736 512
    h372736 checked_372736
  have h373760 := Scan.chunk_sound context_valid facts instructions 373248 512
    h373248 checked_373248
  have h374272 := Scan.chunk_sound context_valid facts instructions 373760 512
    h373760 checked_373760
  have h374784 := Scan.chunk_sound context_valid facts instructions 374272 512
    h374272 checked_374272
  have h375296 := Scan.chunk_sound context_valid facts instructions 374784 512
    h374784 checked_374784
  have h375808 := Scan.chunk_sound context_valid facts instructions 375296 512
    h375296 checked_375296
  have h376320 := Scan.chunk_sound context_valid facts instructions 375808 512
    h375808 checked_375808
  have h376832 := Scan.chunk_sound context_valid facts instructions 376320 512
    h376320 checked_376320
  exact h376832

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCertificate
