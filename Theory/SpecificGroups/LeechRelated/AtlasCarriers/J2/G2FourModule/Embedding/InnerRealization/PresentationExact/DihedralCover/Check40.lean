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
theorem checked_655360 : Scan.checkChunk context facts instructions 655360 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_655872 : Scan.checkChunk context facts instructions 655872 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_656384 : Scan.checkChunk context facts instructions 656384 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_656896 : Scan.checkChunk context facts instructions 656896 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_657408 : Scan.checkChunk context facts instructions 657408 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_657920 : Scan.checkChunk context facts instructions 657920 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_658432 : Scan.checkChunk context facts instructions 658432 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_658944 : Scan.checkChunk context facts instructions 658944 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_659456 : Scan.checkChunk context facts instructions 659456 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_659968 : Scan.checkChunk context facts instructions 659968 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_660480 : Scan.checkChunk context facts instructions 660480 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_660992 : Scan.checkChunk context facts instructions 660992 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_661504 : Scan.checkChunk context facts instructions 661504 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_662016 : Scan.checkChunk context facts instructions 662016 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_662528 : Scan.checkChunk context facts instructions 662528 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_663040 : Scan.checkChunk context facts instructions 663040 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_663552 : Scan.checkChunk context facts instructions 663552 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_664064 : Scan.checkChunk context facts instructions 664064 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_664576 : Scan.checkChunk context facts instructions 664576 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_665088 : Scan.checkChunk context facts instructions 665088 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_665600 : Scan.checkChunk context facts instructions 665600 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_666112 : Scan.checkChunk context facts instructions 666112 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_666624 : Scan.checkChunk context facts instructions 666624 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_667136 : Scan.checkChunk context facts instructions 667136 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_667648 : Scan.checkChunk context facts instructions 667648 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_668160 : Scan.checkChunk context facts instructions 668160 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_668672 : Scan.checkChunk context facts instructions 668672 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_669184 : Scan.checkChunk context facts instructions 669184 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_669696 : Scan.checkChunk context facts instructions 669696 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_670208 : Scan.checkChunk context facts instructions 670208 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_670720 : Scan.checkChunk context facts instructions 670720 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_671232 : Scan.checkChunk context facts instructions 671232 512 = true := by
  decide +kernel

theorem sound_655360 (prior : ∀ n, n < 655360 →
    Holds dihedral generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 671744 → Holds dihedral generator (definitions.repr generator) (facts n) := by
  have h655872 := Scan.chunk_sound context_valid facts instructions 655360 512
    prior checked_655360
  have h656384 := Scan.chunk_sound context_valid facts instructions 655872 512
    h655872 checked_655872
  have h656896 := Scan.chunk_sound context_valid facts instructions 656384 512
    h656384 checked_656384
  have h657408 := Scan.chunk_sound context_valid facts instructions 656896 512
    h656896 checked_656896
  have h657920 := Scan.chunk_sound context_valid facts instructions 657408 512
    h657408 checked_657408
  have h658432 := Scan.chunk_sound context_valid facts instructions 657920 512
    h657920 checked_657920
  have h658944 := Scan.chunk_sound context_valid facts instructions 658432 512
    h658432 checked_658432
  have h659456 := Scan.chunk_sound context_valid facts instructions 658944 512
    h658944 checked_658944
  have h659968 := Scan.chunk_sound context_valid facts instructions 659456 512
    h659456 checked_659456
  have h660480 := Scan.chunk_sound context_valid facts instructions 659968 512
    h659968 checked_659968
  have h660992 := Scan.chunk_sound context_valid facts instructions 660480 512
    h660480 checked_660480
  have h661504 := Scan.chunk_sound context_valid facts instructions 660992 512
    h660992 checked_660992
  have h662016 := Scan.chunk_sound context_valid facts instructions 661504 512
    h661504 checked_661504
  have h662528 := Scan.chunk_sound context_valid facts instructions 662016 512
    h662016 checked_662016
  have h663040 := Scan.chunk_sound context_valid facts instructions 662528 512
    h662528 checked_662528
  have h663552 := Scan.chunk_sound context_valid facts instructions 663040 512
    h663040 checked_663040
  have h664064 := Scan.chunk_sound context_valid facts instructions 663552 512
    h663552 checked_663552
  have h664576 := Scan.chunk_sound context_valid facts instructions 664064 512
    h664064 checked_664064
  have h665088 := Scan.chunk_sound context_valid facts instructions 664576 512
    h664576 checked_664576
  have h665600 := Scan.chunk_sound context_valid facts instructions 665088 512
    h665088 checked_665088
  have h666112 := Scan.chunk_sound context_valid facts instructions 665600 512
    h665600 checked_665600
  have h666624 := Scan.chunk_sound context_valid facts instructions 666112 512
    h666112 checked_666112
  have h667136 := Scan.chunk_sound context_valid facts instructions 666624 512
    h666624 checked_666624
  have h667648 := Scan.chunk_sound context_valid facts instructions 667136 512
    h667136 checked_667136
  have h668160 := Scan.chunk_sound context_valid facts instructions 667648 512
    h667648 checked_667648
  have h668672 := Scan.chunk_sound context_valid facts instructions 668160 512
    h668160 checked_668160
  have h669184 := Scan.chunk_sound context_valid facts instructions 668672 512
    h668672 checked_668672
  have h669696 := Scan.chunk_sound context_valid facts instructions 669184 512
    h669184 checked_669184
  have h670208 := Scan.chunk_sound context_valid facts instructions 669696 512
    h669696 checked_669696
  have h670720 := Scan.chunk_sound context_valid facts instructions 670208 512
    h670208 checked_670208
  have h671232 := Scan.chunk_sound context_valid facts instructions 670720 512
    h670720 checked_670720
  have h671744 := Scan.chunk_sound context_valid facts instructions 671232 512
    h671232 checked_671232
  exact h671744

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCertificate
