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
theorem checked_638976 : Scan.checkChunk context facts instructions 638976 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_639488 : Scan.checkChunk context facts instructions 639488 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_640000 : Scan.checkChunk context facts instructions 640000 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_640512 : Scan.checkChunk context facts instructions 640512 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_641024 : Scan.checkChunk context facts instructions 641024 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_641536 : Scan.checkChunk context facts instructions 641536 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_642048 : Scan.checkChunk context facts instructions 642048 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_642560 : Scan.checkChunk context facts instructions 642560 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_643072 : Scan.checkChunk context facts instructions 643072 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_643584 : Scan.checkChunk context facts instructions 643584 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_644096 : Scan.checkChunk context facts instructions 644096 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_644608 : Scan.checkChunk context facts instructions 644608 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_645120 : Scan.checkChunk context facts instructions 645120 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_645632 : Scan.checkChunk context facts instructions 645632 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_646144 : Scan.checkChunk context facts instructions 646144 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_646656 : Scan.checkChunk context facts instructions 646656 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_647168 : Scan.checkChunk context facts instructions 647168 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_647680 : Scan.checkChunk context facts instructions 647680 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_648192 : Scan.checkChunk context facts instructions 648192 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_648704 : Scan.checkChunk context facts instructions 648704 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_649216 : Scan.checkChunk context facts instructions 649216 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_649728 : Scan.checkChunk context facts instructions 649728 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_650240 : Scan.checkChunk context facts instructions 650240 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_650752 : Scan.checkChunk context facts instructions 650752 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_651264 : Scan.checkChunk context facts instructions 651264 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_651776 : Scan.checkChunk context facts instructions 651776 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_652288 : Scan.checkChunk context facts instructions 652288 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_652800 : Scan.checkChunk context facts instructions 652800 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_653312 : Scan.checkChunk context facts instructions 653312 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_653824 : Scan.checkChunk context facts instructions 653824 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_654336 : Scan.checkChunk context facts instructions 654336 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_654848 : Scan.checkChunk context facts instructions 654848 512 = true := by
  decide +kernel

theorem sound_638976 (prior : ∀ n, n < 638976 →
    Holds dihedral generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 655360 → Holds dihedral generator (definitions.repr generator) (facts n) := by
  have h639488 := Scan.chunk_sound context_valid facts instructions 638976 512
    prior checked_638976
  have h640000 := Scan.chunk_sound context_valid facts instructions 639488 512
    h639488 checked_639488
  have h640512 := Scan.chunk_sound context_valid facts instructions 640000 512
    h640000 checked_640000
  have h641024 := Scan.chunk_sound context_valid facts instructions 640512 512
    h640512 checked_640512
  have h641536 := Scan.chunk_sound context_valid facts instructions 641024 512
    h641024 checked_641024
  have h642048 := Scan.chunk_sound context_valid facts instructions 641536 512
    h641536 checked_641536
  have h642560 := Scan.chunk_sound context_valid facts instructions 642048 512
    h642048 checked_642048
  have h643072 := Scan.chunk_sound context_valid facts instructions 642560 512
    h642560 checked_642560
  have h643584 := Scan.chunk_sound context_valid facts instructions 643072 512
    h643072 checked_643072
  have h644096 := Scan.chunk_sound context_valid facts instructions 643584 512
    h643584 checked_643584
  have h644608 := Scan.chunk_sound context_valid facts instructions 644096 512
    h644096 checked_644096
  have h645120 := Scan.chunk_sound context_valid facts instructions 644608 512
    h644608 checked_644608
  have h645632 := Scan.chunk_sound context_valid facts instructions 645120 512
    h645120 checked_645120
  have h646144 := Scan.chunk_sound context_valid facts instructions 645632 512
    h645632 checked_645632
  have h646656 := Scan.chunk_sound context_valid facts instructions 646144 512
    h646144 checked_646144
  have h647168 := Scan.chunk_sound context_valid facts instructions 646656 512
    h646656 checked_646656
  have h647680 := Scan.chunk_sound context_valid facts instructions 647168 512
    h647168 checked_647168
  have h648192 := Scan.chunk_sound context_valid facts instructions 647680 512
    h647680 checked_647680
  have h648704 := Scan.chunk_sound context_valid facts instructions 648192 512
    h648192 checked_648192
  have h649216 := Scan.chunk_sound context_valid facts instructions 648704 512
    h648704 checked_648704
  have h649728 := Scan.chunk_sound context_valid facts instructions 649216 512
    h649216 checked_649216
  have h650240 := Scan.chunk_sound context_valid facts instructions 649728 512
    h649728 checked_649728
  have h650752 := Scan.chunk_sound context_valid facts instructions 650240 512
    h650240 checked_650240
  have h651264 := Scan.chunk_sound context_valid facts instructions 650752 512
    h650752 checked_650752
  have h651776 := Scan.chunk_sound context_valid facts instructions 651264 512
    h651264 checked_651264
  have h652288 := Scan.chunk_sound context_valid facts instructions 651776 512
    h651776 checked_651776
  have h652800 := Scan.chunk_sound context_valid facts instructions 652288 512
    h652288 checked_652288
  have h653312 := Scan.chunk_sound context_valid facts instructions 652800 512
    h652800 checked_652800
  have h653824 := Scan.chunk_sound context_valid facts instructions 653312 512
    h653312 checked_653312
  have h654336 := Scan.chunk_sound context_valid facts instructions 653824 512
    h653824 checked_653824
  have h654848 := Scan.chunk_sound context_valid facts instructions 654336 512
    h654336 checked_654336
  have h655360 := Scan.chunk_sound context_valid facts instructions 654848 512
    h654848 checked_654848
  exact h655360

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCertificate
