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
theorem checked_507904 : Scan.checkChunk context facts instructions 507904 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_508416 : Scan.checkChunk context facts instructions 508416 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_508928 : Scan.checkChunk context facts instructions 508928 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_509440 : Scan.checkChunk context facts instructions 509440 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_509952 : Scan.checkChunk context facts instructions 509952 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_510464 : Scan.checkChunk context facts instructions 510464 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_510976 : Scan.checkChunk context facts instructions 510976 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_511488 : Scan.checkChunk context facts instructions 511488 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_512000 : Scan.checkChunk context facts instructions 512000 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_512512 : Scan.checkChunk context facts instructions 512512 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_513024 : Scan.checkChunk context facts instructions 513024 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_513536 : Scan.checkChunk context facts instructions 513536 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_514048 : Scan.checkChunk context facts instructions 514048 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_514560 : Scan.checkChunk context facts instructions 514560 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_515072 : Scan.checkChunk context facts instructions 515072 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_515584 : Scan.checkChunk context facts instructions 515584 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_516096 : Scan.checkChunk context facts instructions 516096 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_516608 : Scan.checkChunk context facts instructions 516608 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_517120 : Scan.checkChunk context facts instructions 517120 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_517632 : Scan.checkChunk context facts instructions 517632 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_518144 : Scan.checkChunk context facts instructions 518144 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_518656 : Scan.checkChunk context facts instructions 518656 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_519168 : Scan.checkChunk context facts instructions 519168 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_519680 : Scan.checkChunk context facts instructions 519680 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_520192 : Scan.checkChunk context facts instructions 520192 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_520704 : Scan.checkChunk context facts instructions 520704 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_521216 : Scan.checkChunk context facts instructions 521216 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_521728 : Scan.checkChunk context facts instructions 521728 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_522240 : Scan.checkChunk context facts instructions 522240 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_522752 : Scan.checkChunk context facts instructions 522752 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_523264 : Scan.checkChunk context facts instructions 523264 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_523776 : Scan.checkChunk context facts instructions 523776 512 = true := by
  decide +kernel

theorem sound_507904 (prior : ∀ n, n < 507904 →
    Holds dihedral generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 524288 → Holds dihedral generator (definitions.repr generator) (facts n) := by
  have h508416 := Scan.chunk_sound context_valid facts instructions 507904 512
    prior checked_507904
  have h508928 := Scan.chunk_sound context_valid facts instructions 508416 512
    h508416 checked_508416
  have h509440 := Scan.chunk_sound context_valid facts instructions 508928 512
    h508928 checked_508928
  have h509952 := Scan.chunk_sound context_valid facts instructions 509440 512
    h509440 checked_509440
  have h510464 := Scan.chunk_sound context_valid facts instructions 509952 512
    h509952 checked_509952
  have h510976 := Scan.chunk_sound context_valid facts instructions 510464 512
    h510464 checked_510464
  have h511488 := Scan.chunk_sound context_valid facts instructions 510976 512
    h510976 checked_510976
  have h512000 := Scan.chunk_sound context_valid facts instructions 511488 512
    h511488 checked_511488
  have h512512 := Scan.chunk_sound context_valid facts instructions 512000 512
    h512000 checked_512000
  have h513024 := Scan.chunk_sound context_valid facts instructions 512512 512
    h512512 checked_512512
  have h513536 := Scan.chunk_sound context_valid facts instructions 513024 512
    h513024 checked_513024
  have h514048 := Scan.chunk_sound context_valid facts instructions 513536 512
    h513536 checked_513536
  have h514560 := Scan.chunk_sound context_valid facts instructions 514048 512
    h514048 checked_514048
  have h515072 := Scan.chunk_sound context_valid facts instructions 514560 512
    h514560 checked_514560
  have h515584 := Scan.chunk_sound context_valid facts instructions 515072 512
    h515072 checked_515072
  have h516096 := Scan.chunk_sound context_valid facts instructions 515584 512
    h515584 checked_515584
  have h516608 := Scan.chunk_sound context_valid facts instructions 516096 512
    h516096 checked_516096
  have h517120 := Scan.chunk_sound context_valid facts instructions 516608 512
    h516608 checked_516608
  have h517632 := Scan.chunk_sound context_valid facts instructions 517120 512
    h517120 checked_517120
  have h518144 := Scan.chunk_sound context_valid facts instructions 517632 512
    h517632 checked_517632
  have h518656 := Scan.chunk_sound context_valid facts instructions 518144 512
    h518144 checked_518144
  have h519168 := Scan.chunk_sound context_valid facts instructions 518656 512
    h518656 checked_518656
  have h519680 := Scan.chunk_sound context_valid facts instructions 519168 512
    h519168 checked_519168
  have h520192 := Scan.chunk_sound context_valid facts instructions 519680 512
    h519680 checked_519680
  have h520704 := Scan.chunk_sound context_valid facts instructions 520192 512
    h520192 checked_520192
  have h521216 := Scan.chunk_sound context_valid facts instructions 520704 512
    h520704 checked_520704
  have h521728 := Scan.chunk_sound context_valid facts instructions 521216 512
    h521216 checked_521216
  have h522240 := Scan.chunk_sound context_valid facts instructions 521728 512
    h521728 checked_521728
  have h522752 := Scan.chunk_sound context_valid facts instructions 522240 512
    h522240 checked_522240
  have h523264 := Scan.chunk_sound context_valid facts instructions 522752 512
    h522752 checked_522752
  have h523776 := Scan.chunk_sound context_valid facts instructions 523264 512
    h523264 checked_523264
  have h524288 := Scan.chunk_sound context_valid facts instructions 523776 512
    h523776 checked_523776
  exact h524288

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCertificate
