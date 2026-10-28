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
theorem checked_524288 : Scan.checkChunk context facts instructions 524288 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_524800 : Scan.checkChunk context facts instructions 524800 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_525312 : Scan.checkChunk context facts instructions 525312 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_525824 : Scan.checkChunk context facts instructions 525824 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_526336 : Scan.checkChunk context facts instructions 526336 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_526848 : Scan.checkChunk context facts instructions 526848 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_527360 : Scan.checkChunk context facts instructions 527360 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_527872 : Scan.checkChunk context facts instructions 527872 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_528384 : Scan.checkChunk context facts instructions 528384 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_528896 : Scan.checkChunk context facts instructions 528896 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_529408 : Scan.checkChunk context facts instructions 529408 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_529920 : Scan.checkChunk context facts instructions 529920 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_530432 : Scan.checkChunk context facts instructions 530432 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_530944 : Scan.checkChunk context facts instructions 530944 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_531456 : Scan.checkChunk context facts instructions 531456 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_531968 : Scan.checkChunk context facts instructions 531968 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_532480 : Scan.checkChunk context facts instructions 532480 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_532992 : Scan.checkChunk context facts instructions 532992 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_533504 : Scan.checkChunk context facts instructions 533504 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_534016 : Scan.checkChunk context facts instructions 534016 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_534528 : Scan.checkChunk context facts instructions 534528 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_535040 : Scan.checkChunk context facts instructions 535040 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_535552 : Scan.checkChunk context facts instructions 535552 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_536064 : Scan.checkChunk context facts instructions 536064 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_536576 : Scan.checkChunk context facts instructions 536576 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_537088 : Scan.checkChunk context facts instructions 537088 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_537600 : Scan.checkChunk context facts instructions 537600 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_538112 : Scan.checkChunk context facts instructions 538112 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_538624 : Scan.checkChunk context facts instructions 538624 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_539136 : Scan.checkChunk context facts instructions 539136 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_539648 : Scan.checkChunk context facts instructions 539648 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_540160 : Scan.checkChunk context facts instructions 540160 512 = true := by
  decide +kernel

theorem sound_524288 (prior : ∀ n, n < 524288 →
    Holds dihedral generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 540672 → Holds dihedral generator (definitions.repr generator) (facts n) := by
  have h524800 := Scan.chunk_sound context_valid facts instructions 524288 512
    prior checked_524288
  have h525312 := Scan.chunk_sound context_valid facts instructions 524800 512
    h524800 checked_524800
  have h525824 := Scan.chunk_sound context_valid facts instructions 525312 512
    h525312 checked_525312
  have h526336 := Scan.chunk_sound context_valid facts instructions 525824 512
    h525824 checked_525824
  have h526848 := Scan.chunk_sound context_valid facts instructions 526336 512
    h526336 checked_526336
  have h527360 := Scan.chunk_sound context_valid facts instructions 526848 512
    h526848 checked_526848
  have h527872 := Scan.chunk_sound context_valid facts instructions 527360 512
    h527360 checked_527360
  have h528384 := Scan.chunk_sound context_valid facts instructions 527872 512
    h527872 checked_527872
  have h528896 := Scan.chunk_sound context_valid facts instructions 528384 512
    h528384 checked_528384
  have h529408 := Scan.chunk_sound context_valid facts instructions 528896 512
    h528896 checked_528896
  have h529920 := Scan.chunk_sound context_valid facts instructions 529408 512
    h529408 checked_529408
  have h530432 := Scan.chunk_sound context_valid facts instructions 529920 512
    h529920 checked_529920
  have h530944 := Scan.chunk_sound context_valid facts instructions 530432 512
    h530432 checked_530432
  have h531456 := Scan.chunk_sound context_valid facts instructions 530944 512
    h530944 checked_530944
  have h531968 := Scan.chunk_sound context_valid facts instructions 531456 512
    h531456 checked_531456
  have h532480 := Scan.chunk_sound context_valid facts instructions 531968 512
    h531968 checked_531968
  have h532992 := Scan.chunk_sound context_valid facts instructions 532480 512
    h532480 checked_532480
  have h533504 := Scan.chunk_sound context_valid facts instructions 532992 512
    h532992 checked_532992
  have h534016 := Scan.chunk_sound context_valid facts instructions 533504 512
    h533504 checked_533504
  have h534528 := Scan.chunk_sound context_valid facts instructions 534016 512
    h534016 checked_534016
  have h535040 := Scan.chunk_sound context_valid facts instructions 534528 512
    h534528 checked_534528
  have h535552 := Scan.chunk_sound context_valid facts instructions 535040 512
    h535040 checked_535040
  have h536064 := Scan.chunk_sound context_valid facts instructions 535552 512
    h535552 checked_535552
  have h536576 := Scan.chunk_sound context_valid facts instructions 536064 512
    h536064 checked_536064
  have h537088 := Scan.chunk_sound context_valid facts instructions 536576 512
    h536576 checked_536576
  have h537600 := Scan.chunk_sound context_valid facts instructions 537088 512
    h537088 checked_537088
  have h538112 := Scan.chunk_sound context_valid facts instructions 537600 512
    h537600 checked_537600
  have h538624 := Scan.chunk_sound context_valid facts instructions 538112 512
    h538112 checked_538112
  have h539136 := Scan.chunk_sound context_valid facts instructions 538624 512
    h538624 checked_538624
  have h539648 := Scan.chunk_sound context_valid facts instructions 539136 512
    h539136 checked_539136
  have h540160 := Scan.chunk_sound context_valid facts instructions 539648 512
    h539648 checked_539648
  have h540672 := Scan.chunk_sound context_valid facts instructions 540160 512
    h540160 checked_540160
  exact h540672

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCertificate
