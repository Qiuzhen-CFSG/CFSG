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
theorem checked_589824 : Scan.checkChunk context facts instructions 589824 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_590336 : Scan.checkChunk context facts instructions 590336 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_590848 : Scan.checkChunk context facts instructions 590848 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_591360 : Scan.checkChunk context facts instructions 591360 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_591872 : Scan.checkChunk context facts instructions 591872 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_592384 : Scan.checkChunk context facts instructions 592384 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_592896 : Scan.checkChunk context facts instructions 592896 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_593408 : Scan.checkChunk context facts instructions 593408 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_593920 : Scan.checkChunk context facts instructions 593920 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_594432 : Scan.checkChunk context facts instructions 594432 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_594944 : Scan.checkChunk context facts instructions 594944 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_595456 : Scan.checkChunk context facts instructions 595456 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_595968 : Scan.checkChunk context facts instructions 595968 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_596480 : Scan.checkChunk context facts instructions 596480 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_596992 : Scan.checkChunk context facts instructions 596992 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_597504 : Scan.checkChunk context facts instructions 597504 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_598016 : Scan.checkChunk context facts instructions 598016 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_598528 : Scan.checkChunk context facts instructions 598528 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_599040 : Scan.checkChunk context facts instructions 599040 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_599552 : Scan.checkChunk context facts instructions 599552 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_600064 : Scan.checkChunk context facts instructions 600064 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_600576 : Scan.checkChunk context facts instructions 600576 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_601088 : Scan.checkChunk context facts instructions 601088 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_601600 : Scan.checkChunk context facts instructions 601600 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_602112 : Scan.checkChunk context facts instructions 602112 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_602624 : Scan.checkChunk context facts instructions 602624 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_603136 : Scan.checkChunk context facts instructions 603136 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_603648 : Scan.checkChunk context facts instructions 603648 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_604160 : Scan.checkChunk context facts instructions 604160 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_604672 : Scan.checkChunk context facts instructions 604672 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_605184 : Scan.checkChunk context facts instructions 605184 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_605696 : Scan.checkChunk context facts instructions 605696 512 = true := by
  decide +kernel

theorem sound_589824 (prior : ∀ n, n < 589824 →
    Holds dihedral generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 606208 → Holds dihedral generator (definitions.repr generator) (facts n) := by
  have h590336 := Scan.chunk_sound context_valid facts instructions 589824 512
    prior checked_589824
  have h590848 := Scan.chunk_sound context_valid facts instructions 590336 512
    h590336 checked_590336
  have h591360 := Scan.chunk_sound context_valid facts instructions 590848 512
    h590848 checked_590848
  have h591872 := Scan.chunk_sound context_valid facts instructions 591360 512
    h591360 checked_591360
  have h592384 := Scan.chunk_sound context_valid facts instructions 591872 512
    h591872 checked_591872
  have h592896 := Scan.chunk_sound context_valid facts instructions 592384 512
    h592384 checked_592384
  have h593408 := Scan.chunk_sound context_valid facts instructions 592896 512
    h592896 checked_592896
  have h593920 := Scan.chunk_sound context_valid facts instructions 593408 512
    h593408 checked_593408
  have h594432 := Scan.chunk_sound context_valid facts instructions 593920 512
    h593920 checked_593920
  have h594944 := Scan.chunk_sound context_valid facts instructions 594432 512
    h594432 checked_594432
  have h595456 := Scan.chunk_sound context_valid facts instructions 594944 512
    h594944 checked_594944
  have h595968 := Scan.chunk_sound context_valid facts instructions 595456 512
    h595456 checked_595456
  have h596480 := Scan.chunk_sound context_valid facts instructions 595968 512
    h595968 checked_595968
  have h596992 := Scan.chunk_sound context_valid facts instructions 596480 512
    h596480 checked_596480
  have h597504 := Scan.chunk_sound context_valid facts instructions 596992 512
    h596992 checked_596992
  have h598016 := Scan.chunk_sound context_valid facts instructions 597504 512
    h597504 checked_597504
  have h598528 := Scan.chunk_sound context_valid facts instructions 598016 512
    h598016 checked_598016
  have h599040 := Scan.chunk_sound context_valid facts instructions 598528 512
    h598528 checked_598528
  have h599552 := Scan.chunk_sound context_valid facts instructions 599040 512
    h599040 checked_599040
  have h600064 := Scan.chunk_sound context_valid facts instructions 599552 512
    h599552 checked_599552
  have h600576 := Scan.chunk_sound context_valid facts instructions 600064 512
    h600064 checked_600064
  have h601088 := Scan.chunk_sound context_valid facts instructions 600576 512
    h600576 checked_600576
  have h601600 := Scan.chunk_sound context_valid facts instructions 601088 512
    h601088 checked_601088
  have h602112 := Scan.chunk_sound context_valid facts instructions 601600 512
    h601600 checked_601600
  have h602624 := Scan.chunk_sound context_valid facts instructions 602112 512
    h602112 checked_602112
  have h603136 := Scan.chunk_sound context_valid facts instructions 602624 512
    h602624 checked_602624
  have h603648 := Scan.chunk_sound context_valid facts instructions 603136 512
    h603136 checked_603136
  have h604160 := Scan.chunk_sound context_valid facts instructions 603648 512
    h603648 checked_603648
  have h604672 := Scan.chunk_sound context_valid facts instructions 604160 512
    h604160 checked_604160
  have h605184 := Scan.chunk_sound context_valid facts instructions 604672 512
    h604672 checked_604672
  have h605696 := Scan.chunk_sound context_valid facts instructions 605184 512
    h605184 checked_605184
  have h606208 := Scan.chunk_sound context_valid facts instructions 605696 512
    h605696 checked_605696
  exact h606208

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCertificate
