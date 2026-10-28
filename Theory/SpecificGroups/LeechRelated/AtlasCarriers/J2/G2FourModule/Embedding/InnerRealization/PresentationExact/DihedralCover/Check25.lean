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
theorem checked_409600 : Scan.checkChunk context facts instructions 409600 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_410112 : Scan.checkChunk context facts instructions 410112 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_410624 : Scan.checkChunk context facts instructions 410624 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_411136 : Scan.checkChunk context facts instructions 411136 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_411648 : Scan.checkChunk context facts instructions 411648 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_412160 : Scan.checkChunk context facts instructions 412160 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_412672 : Scan.checkChunk context facts instructions 412672 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_413184 : Scan.checkChunk context facts instructions 413184 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_413696 : Scan.checkChunk context facts instructions 413696 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_414208 : Scan.checkChunk context facts instructions 414208 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_414720 : Scan.checkChunk context facts instructions 414720 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_415232 : Scan.checkChunk context facts instructions 415232 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_415744 : Scan.checkChunk context facts instructions 415744 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_416256 : Scan.checkChunk context facts instructions 416256 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_416768 : Scan.checkChunk context facts instructions 416768 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_417280 : Scan.checkChunk context facts instructions 417280 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_417792 : Scan.checkChunk context facts instructions 417792 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_418304 : Scan.checkChunk context facts instructions 418304 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_418816 : Scan.checkChunk context facts instructions 418816 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_419328 : Scan.checkChunk context facts instructions 419328 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_419840 : Scan.checkChunk context facts instructions 419840 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_420352 : Scan.checkChunk context facts instructions 420352 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_420864 : Scan.checkChunk context facts instructions 420864 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_421376 : Scan.checkChunk context facts instructions 421376 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_421888 : Scan.checkChunk context facts instructions 421888 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_422400 : Scan.checkChunk context facts instructions 422400 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_422912 : Scan.checkChunk context facts instructions 422912 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_423424 : Scan.checkChunk context facts instructions 423424 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_423936 : Scan.checkChunk context facts instructions 423936 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_424448 : Scan.checkChunk context facts instructions 424448 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_424960 : Scan.checkChunk context facts instructions 424960 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_425472 : Scan.checkChunk context facts instructions 425472 512 = true := by
  decide +kernel

theorem sound_409600 (prior : ∀ n, n < 409600 →
    Holds dihedral generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 425984 → Holds dihedral generator (definitions.repr generator) (facts n) := by
  have h410112 := Scan.chunk_sound context_valid facts instructions 409600 512
    prior checked_409600
  have h410624 := Scan.chunk_sound context_valid facts instructions 410112 512
    h410112 checked_410112
  have h411136 := Scan.chunk_sound context_valid facts instructions 410624 512
    h410624 checked_410624
  have h411648 := Scan.chunk_sound context_valid facts instructions 411136 512
    h411136 checked_411136
  have h412160 := Scan.chunk_sound context_valid facts instructions 411648 512
    h411648 checked_411648
  have h412672 := Scan.chunk_sound context_valid facts instructions 412160 512
    h412160 checked_412160
  have h413184 := Scan.chunk_sound context_valid facts instructions 412672 512
    h412672 checked_412672
  have h413696 := Scan.chunk_sound context_valid facts instructions 413184 512
    h413184 checked_413184
  have h414208 := Scan.chunk_sound context_valid facts instructions 413696 512
    h413696 checked_413696
  have h414720 := Scan.chunk_sound context_valid facts instructions 414208 512
    h414208 checked_414208
  have h415232 := Scan.chunk_sound context_valid facts instructions 414720 512
    h414720 checked_414720
  have h415744 := Scan.chunk_sound context_valid facts instructions 415232 512
    h415232 checked_415232
  have h416256 := Scan.chunk_sound context_valid facts instructions 415744 512
    h415744 checked_415744
  have h416768 := Scan.chunk_sound context_valid facts instructions 416256 512
    h416256 checked_416256
  have h417280 := Scan.chunk_sound context_valid facts instructions 416768 512
    h416768 checked_416768
  have h417792 := Scan.chunk_sound context_valid facts instructions 417280 512
    h417280 checked_417280
  have h418304 := Scan.chunk_sound context_valid facts instructions 417792 512
    h417792 checked_417792
  have h418816 := Scan.chunk_sound context_valid facts instructions 418304 512
    h418304 checked_418304
  have h419328 := Scan.chunk_sound context_valid facts instructions 418816 512
    h418816 checked_418816
  have h419840 := Scan.chunk_sound context_valid facts instructions 419328 512
    h419328 checked_419328
  have h420352 := Scan.chunk_sound context_valid facts instructions 419840 512
    h419840 checked_419840
  have h420864 := Scan.chunk_sound context_valid facts instructions 420352 512
    h420352 checked_420352
  have h421376 := Scan.chunk_sound context_valid facts instructions 420864 512
    h420864 checked_420864
  have h421888 := Scan.chunk_sound context_valid facts instructions 421376 512
    h421376 checked_421376
  have h422400 := Scan.chunk_sound context_valid facts instructions 421888 512
    h421888 checked_421888
  have h422912 := Scan.chunk_sound context_valid facts instructions 422400 512
    h422400 checked_422400
  have h423424 := Scan.chunk_sound context_valid facts instructions 422912 512
    h422912 checked_422912
  have h423936 := Scan.chunk_sound context_valid facts instructions 423424 512
    h423424 checked_423424
  have h424448 := Scan.chunk_sound context_valid facts instructions 423936 512
    h423936 checked_423936
  have h424960 := Scan.chunk_sound context_valid facts instructions 424448 512
    h424448 checked_424448
  have h425472 := Scan.chunk_sound context_valid facts instructions 424960 512
    h424960 checked_424960
  have h425984 := Scan.chunk_sound context_valid facts instructions 425472 512
    h425472 checked_425472
  exact h425984

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCertificate
