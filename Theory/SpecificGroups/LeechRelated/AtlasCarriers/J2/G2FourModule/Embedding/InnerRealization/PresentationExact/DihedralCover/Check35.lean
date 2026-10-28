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
theorem checked_573440 : Scan.checkChunk context facts instructions 573440 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_573952 : Scan.checkChunk context facts instructions 573952 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_574464 : Scan.checkChunk context facts instructions 574464 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_574976 : Scan.checkChunk context facts instructions 574976 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_575488 : Scan.checkChunk context facts instructions 575488 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_576000 : Scan.checkChunk context facts instructions 576000 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_576512 : Scan.checkChunk context facts instructions 576512 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_577024 : Scan.checkChunk context facts instructions 577024 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_577536 : Scan.checkChunk context facts instructions 577536 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_578048 : Scan.checkChunk context facts instructions 578048 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_578560 : Scan.checkChunk context facts instructions 578560 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_579072 : Scan.checkChunk context facts instructions 579072 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_579584 : Scan.checkChunk context facts instructions 579584 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_580096 : Scan.checkChunk context facts instructions 580096 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_580608 : Scan.checkChunk context facts instructions 580608 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_581120 : Scan.checkChunk context facts instructions 581120 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_581632 : Scan.checkChunk context facts instructions 581632 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_582144 : Scan.checkChunk context facts instructions 582144 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_582656 : Scan.checkChunk context facts instructions 582656 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_583168 : Scan.checkChunk context facts instructions 583168 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_583680 : Scan.checkChunk context facts instructions 583680 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_584192 : Scan.checkChunk context facts instructions 584192 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_584704 : Scan.checkChunk context facts instructions 584704 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_585216 : Scan.checkChunk context facts instructions 585216 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_585728 : Scan.checkChunk context facts instructions 585728 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_586240 : Scan.checkChunk context facts instructions 586240 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_586752 : Scan.checkChunk context facts instructions 586752 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_587264 : Scan.checkChunk context facts instructions 587264 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_587776 : Scan.checkChunk context facts instructions 587776 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_588288 : Scan.checkChunk context facts instructions 588288 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_588800 : Scan.checkChunk context facts instructions 588800 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_589312 : Scan.checkChunk context facts instructions 589312 512 = true := by
  decide +kernel

theorem sound_573440 (prior : ∀ n, n < 573440 →
    Holds dihedral generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 589824 → Holds dihedral generator (definitions.repr generator) (facts n) := by
  have h573952 := Scan.chunk_sound context_valid facts instructions 573440 512
    prior checked_573440
  have h574464 := Scan.chunk_sound context_valid facts instructions 573952 512
    h573952 checked_573952
  have h574976 := Scan.chunk_sound context_valid facts instructions 574464 512
    h574464 checked_574464
  have h575488 := Scan.chunk_sound context_valid facts instructions 574976 512
    h574976 checked_574976
  have h576000 := Scan.chunk_sound context_valid facts instructions 575488 512
    h575488 checked_575488
  have h576512 := Scan.chunk_sound context_valid facts instructions 576000 512
    h576000 checked_576000
  have h577024 := Scan.chunk_sound context_valid facts instructions 576512 512
    h576512 checked_576512
  have h577536 := Scan.chunk_sound context_valid facts instructions 577024 512
    h577024 checked_577024
  have h578048 := Scan.chunk_sound context_valid facts instructions 577536 512
    h577536 checked_577536
  have h578560 := Scan.chunk_sound context_valid facts instructions 578048 512
    h578048 checked_578048
  have h579072 := Scan.chunk_sound context_valid facts instructions 578560 512
    h578560 checked_578560
  have h579584 := Scan.chunk_sound context_valid facts instructions 579072 512
    h579072 checked_579072
  have h580096 := Scan.chunk_sound context_valid facts instructions 579584 512
    h579584 checked_579584
  have h580608 := Scan.chunk_sound context_valid facts instructions 580096 512
    h580096 checked_580096
  have h581120 := Scan.chunk_sound context_valid facts instructions 580608 512
    h580608 checked_580608
  have h581632 := Scan.chunk_sound context_valid facts instructions 581120 512
    h581120 checked_581120
  have h582144 := Scan.chunk_sound context_valid facts instructions 581632 512
    h581632 checked_581632
  have h582656 := Scan.chunk_sound context_valid facts instructions 582144 512
    h582144 checked_582144
  have h583168 := Scan.chunk_sound context_valid facts instructions 582656 512
    h582656 checked_582656
  have h583680 := Scan.chunk_sound context_valid facts instructions 583168 512
    h583168 checked_583168
  have h584192 := Scan.chunk_sound context_valid facts instructions 583680 512
    h583680 checked_583680
  have h584704 := Scan.chunk_sound context_valid facts instructions 584192 512
    h584192 checked_584192
  have h585216 := Scan.chunk_sound context_valid facts instructions 584704 512
    h584704 checked_584704
  have h585728 := Scan.chunk_sound context_valid facts instructions 585216 512
    h585216 checked_585216
  have h586240 := Scan.chunk_sound context_valid facts instructions 585728 512
    h585728 checked_585728
  have h586752 := Scan.chunk_sound context_valid facts instructions 586240 512
    h586240 checked_586240
  have h587264 := Scan.chunk_sound context_valid facts instructions 586752 512
    h586752 checked_586752
  have h587776 := Scan.chunk_sound context_valid facts instructions 587264 512
    h587264 checked_587264
  have h588288 := Scan.chunk_sound context_valid facts instructions 587776 512
    h587776 checked_587776
  have h588800 := Scan.chunk_sound context_valid facts instructions 588288 512
    h588288 checked_588288
  have h589312 := Scan.chunk_sound context_valid facts instructions 588800 512
    h588800 checked_588800
  have h589824 := Scan.chunk_sound context_valid facts instructions 589312 512
    h589312 checked_589312
  exact h589824

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCertificate
