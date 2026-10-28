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
theorem checked_458752 : Scan.checkChunk context facts instructions 458752 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_459264 : Scan.checkChunk context facts instructions 459264 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_459776 : Scan.checkChunk context facts instructions 459776 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_460288 : Scan.checkChunk context facts instructions 460288 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_460800 : Scan.checkChunk context facts instructions 460800 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_461312 : Scan.checkChunk context facts instructions 461312 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_461824 : Scan.checkChunk context facts instructions 461824 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_462336 : Scan.checkChunk context facts instructions 462336 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_462848 : Scan.checkChunk context facts instructions 462848 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_463360 : Scan.checkChunk context facts instructions 463360 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_463872 : Scan.checkChunk context facts instructions 463872 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_464384 : Scan.checkChunk context facts instructions 464384 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_464896 : Scan.checkChunk context facts instructions 464896 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_465408 : Scan.checkChunk context facts instructions 465408 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_465920 : Scan.checkChunk context facts instructions 465920 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_466432 : Scan.checkChunk context facts instructions 466432 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_466944 : Scan.checkChunk context facts instructions 466944 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_467456 : Scan.checkChunk context facts instructions 467456 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_467968 : Scan.checkChunk context facts instructions 467968 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_468480 : Scan.checkChunk context facts instructions 468480 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_468992 : Scan.checkChunk context facts instructions 468992 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_469504 : Scan.checkChunk context facts instructions 469504 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_470016 : Scan.checkChunk context facts instructions 470016 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_470528 : Scan.checkChunk context facts instructions 470528 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_471040 : Scan.checkChunk context facts instructions 471040 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_471552 : Scan.checkChunk context facts instructions 471552 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_472064 : Scan.checkChunk context facts instructions 472064 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_472576 : Scan.checkChunk context facts instructions 472576 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_473088 : Scan.checkChunk context facts instructions 473088 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_473600 : Scan.checkChunk context facts instructions 473600 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_474112 : Scan.checkChunk context facts instructions 474112 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_474624 : Scan.checkChunk context facts instructions 474624 512 = true := by
  decide +kernel

theorem sound_458752 (prior : ∀ n, n < 458752 →
    Holds dihedral generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 475136 → Holds dihedral generator (definitions.repr generator) (facts n) := by
  have h459264 := Scan.chunk_sound context_valid facts instructions 458752 512
    prior checked_458752
  have h459776 := Scan.chunk_sound context_valid facts instructions 459264 512
    h459264 checked_459264
  have h460288 := Scan.chunk_sound context_valid facts instructions 459776 512
    h459776 checked_459776
  have h460800 := Scan.chunk_sound context_valid facts instructions 460288 512
    h460288 checked_460288
  have h461312 := Scan.chunk_sound context_valid facts instructions 460800 512
    h460800 checked_460800
  have h461824 := Scan.chunk_sound context_valid facts instructions 461312 512
    h461312 checked_461312
  have h462336 := Scan.chunk_sound context_valid facts instructions 461824 512
    h461824 checked_461824
  have h462848 := Scan.chunk_sound context_valid facts instructions 462336 512
    h462336 checked_462336
  have h463360 := Scan.chunk_sound context_valid facts instructions 462848 512
    h462848 checked_462848
  have h463872 := Scan.chunk_sound context_valid facts instructions 463360 512
    h463360 checked_463360
  have h464384 := Scan.chunk_sound context_valid facts instructions 463872 512
    h463872 checked_463872
  have h464896 := Scan.chunk_sound context_valid facts instructions 464384 512
    h464384 checked_464384
  have h465408 := Scan.chunk_sound context_valid facts instructions 464896 512
    h464896 checked_464896
  have h465920 := Scan.chunk_sound context_valid facts instructions 465408 512
    h465408 checked_465408
  have h466432 := Scan.chunk_sound context_valid facts instructions 465920 512
    h465920 checked_465920
  have h466944 := Scan.chunk_sound context_valid facts instructions 466432 512
    h466432 checked_466432
  have h467456 := Scan.chunk_sound context_valid facts instructions 466944 512
    h466944 checked_466944
  have h467968 := Scan.chunk_sound context_valid facts instructions 467456 512
    h467456 checked_467456
  have h468480 := Scan.chunk_sound context_valid facts instructions 467968 512
    h467968 checked_467968
  have h468992 := Scan.chunk_sound context_valid facts instructions 468480 512
    h468480 checked_468480
  have h469504 := Scan.chunk_sound context_valid facts instructions 468992 512
    h468992 checked_468992
  have h470016 := Scan.chunk_sound context_valid facts instructions 469504 512
    h469504 checked_469504
  have h470528 := Scan.chunk_sound context_valid facts instructions 470016 512
    h470016 checked_470016
  have h471040 := Scan.chunk_sound context_valid facts instructions 470528 512
    h470528 checked_470528
  have h471552 := Scan.chunk_sound context_valid facts instructions 471040 512
    h471040 checked_471040
  have h472064 := Scan.chunk_sound context_valid facts instructions 471552 512
    h471552 checked_471552
  have h472576 := Scan.chunk_sound context_valid facts instructions 472064 512
    h472064 checked_472064
  have h473088 := Scan.chunk_sound context_valid facts instructions 472576 512
    h472576 checked_472576
  have h473600 := Scan.chunk_sound context_valid facts instructions 473088 512
    h473088 checked_473088
  have h474112 := Scan.chunk_sound context_valid facts instructions 473600 512
    h473600 checked_473600
  have h474624 := Scan.chunk_sound context_valid facts instructions 474112 512
    h474112 checked_474112
  have h475136 := Scan.chunk_sound context_valid facts instructions 474624 512
    h474624 checked_474624
  exact h475136

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCertificate
