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
theorem checked_557056 : Scan.checkChunk context facts instructions 557056 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_557568 : Scan.checkChunk context facts instructions 557568 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_558080 : Scan.checkChunk context facts instructions 558080 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_558592 : Scan.checkChunk context facts instructions 558592 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_559104 : Scan.checkChunk context facts instructions 559104 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_559616 : Scan.checkChunk context facts instructions 559616 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_560128 : Scan.checkChunk context facts instructions 560128 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_560640 : Scan.checkChunk context facts instructions 560640 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_561152 : Scan.checkChunk context facts instructions 561152 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_561664 : Scan.checkChunk context facts instructions 561664 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_562176 : Scan.checkChunk context facts instructions 562176 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_562688 : Scan.checkChunk context facts instructions 562688 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_563200 : Scan.checkChunk context facts instructions 563200 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_563712 : Scan.checkChunk context facts instructions 563712 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_564224 : Scan.checkChunk context facts instructions 564224 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_564736 : Scan.checkChunk context facts instructions 564736 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_565248 : Scan.checkChunk context facts instructions 565248 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_565760 : Scan.checkChunk context facts instructions 565760 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_566272 : Scan.checkChunk context facts instructions 566272 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_566784 : Scan.checkChunk context facts instructions 566784 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_567296 : Scan.checkChunk context facts instructions 567296 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_567808 : Scan.checkChunk context facts instructions 567808 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_568320 : Scan.checkChunk context facts instructions 568320 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_568832 : Scan.checkChunk context facts instructions 568832 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_569344 : Scan.checkChunk context facts instructions 569344 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_569856 : Scan.checkChunk context facts instructions 569856 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_570368 : Scan.checkChunk context facts instructions 570368 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_570880 : Scan.checkChunk context facts instructions 570880 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_571392 : Scan.checkChunk context facts instructions 571392 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_571904 : Scan.checkChunk context facts instructions 571904 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_572416 : Scan.checkChunk context facts instructions 572416 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_572928 : Scan.checkChunk context facts instructions 572928 512 = true := by
  decide +kernel

theorem sound_557056 (prior : ∀ n, n < 557056 →
    Holds dihedral generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 573440 → Holds dihedral generator (definitions.repr generator) (facts n) := by
  have h557568 := Scan.chunk_sound context_valid facts instructions 557056 512
    prior checked_557056
  have h558080 := Scan.chunk_sound context_valid facts instructions 557568 512
    h557568 checked_557568
  have h558592 := Scan.chunk_sound context_valid facts instructions 558080 512
    h558080 checked_558080
  have h559104 := Scan.chunk_sound context_valid facts instructions 558592 512
    h558592 checked_558592
  have h559616 := Scan.chunk_sound context_valid facts instructions 559104 512
    h559104 checked_559104
  have h560128 := Scan.chunk_sound context_valid facts instructions 559616 512
    h559616 checked_559616
  have h560640 := Scan.chunk_sound context_valid facts instructions 560128 512
    h560128 checked_560128
  have h561152 := Scan.chunk_sound context_valid facts instructions 560640 512
    h560640 checked_560640
  have h561664 := Scan.chunk_sound context_valid facts instructions 561152 512
    h561152 checked_561152
  have h562176 := Scan.chunk_sound context_valid facts instructions 561664 512
    h561664 checked_561664
  have h562688 := Scan.chunk_sound context_valid facts instructions 562176 512
    h562176 checked_562176
  have h563200 := Scan.chunk_sound context_valid facts instructions 562688 512
    h562688 checked_562688
  have h563712 := Scan.chunk_sound context_valid facts instructions 563200 512
    h563200 checked_563200
  have h564224 := Scan.chunk_sound context_valid facts instructions 563712 512
    h563712 checked_563712
  have h564736 := Scan.chunk_sound context_valid facts instructions 564224 512
    h564224 checked_564224
  have h565248 := Scan.chunk_sound context_valid facts instructions 564736 512
    h564736 checked_564736
  have h565760 := Scan.chunk_sound context_valid facts instructions 565248 512
    h565248 checked_565248
  have h566272 := Scan.chunk_sound context_valid facts instructions 565760 512
    h565760 checked_565760
  have h566784 := Scan.chunk_sound context_valid facts instructions 566272 512
    h566272 checked_566272
  have h567296 := Scan.chunk_sound context_valid facts instructions 566784 512
    h566784 checked_566784
  have h567808 := Scan.chunk_sound context_valid facts instructions 567296 512
    h567296 checked_567296
  have h568320 := Scan.chunk_sound context_valid facts instructions 567808 512
    h567808 checked_567808
  have h568832 := Scan.chunk_sound context_valid facts instructions 568320 512
    h568320 checked_568320
  have h569344 := Scan.chunk_sound context_valid facts instructions 568832 512
    h568832 checked_568832
  have h569856 := Scan.chunk_sound context_valid facts instructions 569344 512
    h569344 checked_569344
  have h570368 := Scan.chunk_sound context_valid facts instructions 569856 512
    h569856 checked_569856
  have h570880 := Scan.chunk_sound context_valid facts instructions 570368 512
    h570368 checked_570368
  have h571392 := Scan.chunk_sound context_valid facts instructions 570880 512
    h570880 checked_570880
  have h571904 := Scan.chunk_sound context_valid facts instructions 571392 512
    h571392 checked_571392
  have h572416 := Scan.chunk_sound context_valid facts instructions 571904 512
    h571904 checked_571904
  have h572928 := Scan.chunk_sound context_valid facts instructions 572416 512
    h572416 checked_572416
  have h573440 := Scan.chunk_sound context_valid facts instructions 572928 512
    h572928 checked_572928
  exact h573440

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCertificate
