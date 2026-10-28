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
theorem checked_442368 : Scan.checkChunk context facts instructions 442368 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_442880 : Scan.checkChunk context facts instructions 442880 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_443392 : Scan.checkChunk context facts instructions 443392 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_443904 : Scan.checkChunk context facts instructions 443904 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_444416 : Scan.checkChunk context facts instructions 444416 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_444928 : Scan.checkChunk context facts instructions 444928 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_445440 : Scan.checkChunk context facts instructions 445440 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_445952 : Scan.checkChunk context facts instructions 445952 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_446464 : Scan.checkChunk context facts instructions 446464 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_446976 : Scan.checkChunk context facts instructions 446976 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_447488 : Scan.checkChunk context facts instructions 447488 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_448000 : Scan.checkChunk context facts instructions 448000 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_448512 : Scan.checkChunk context facts instructions 448512 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_449024 : Scan.checkChunk context facts instructions 449024 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_449536 : Scan.checkChunk context facts instructions 449536 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_450048 : Scan.checkChunk context facts instructions 450048 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_450560 : Scan.checkChunk context facts instructions 450560 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_451072 : Scan.checkChunk context facts instructions 451072 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_451584 : Scan.checkChunk context facts instructions 451584 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_452096 : Scan.checkChunk context facts instructions 452096 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_452608 : Scan.checkChunk context facts instructions 452608 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_453120 : Scan.checkChunk context facts instructions 453120 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_453632 : Scan.checkChunk context facts instructions 453632 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_454144 : Scan.checkChunk context facts instructions 454144 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_454656 : Scan.checkChunk context facts instructions 454656 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_455168 : Scan.checkChunk context facts instructions 455168 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_455680 : Scan.checkChunk context facts instructions 455680 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_456192 : Scan.checkChunk context facts instructions 456192 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_456704 : Scan.checkChunk context facts instructions 456704 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_457216 : Scan.checkChunk context facts instructions 457216 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_457728 : Scan.checkChunk context facts instructions 457728 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_458240 : Scan.checkChunk context facts instructions 458240 512 = true := by
  decide +kernel

theorem sound_442368 (prior : ∀ n, n < 442368 →
    Holds dihedral generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 458752 → Holds dihedral generator (definitions.repr generator) (facts n) := by
  have h442880 := Scan.chunk_sound context_valid facts instructions 442368 512
    prior checked_442368
  have h443392 := Scan.chunk_sound context_valid facts instructions 442880 512
    h442880 checked_442880
  have h443904 := Scan.chunk_sound context_valid facts instructions 443392 512
    h443392 checked_443392
  have h444416 := Scan.chunk_sound context_valid facts instructions 443904 512
    h443904 checked_443904
  have h444928 := Scan.chunk_sound context_valid facts instructions 444416 512
    h444416 checked_444416
  have h445440 := Scan.chunk_sound context_valid facts instructions 444928 512
    h444928 checked_444928
  have h445952 := Scan.chunk_sound context_valid facts instructions 445440 512
    h445440 checked_445440
  have h446464 := Scan.chunk_sound context_valid facts instructions 445952 512
    h445952 checked_445952
  have h446976 := Scan.chunk_sound context_valid facts instructions 446464 512
    h446464 checked_446464
  have h447488 := Scan.chunk_sound context_valid facts instructions 446976 512
    h446976 checked_446976
  have h448000 := Scan.chunk_sound context_valid facts instructions 447488 512
    h447488 checked_447488
  have h448512 := Scan.chunk_sound context_valid facts instructions 448000 512
    h448000 checked_448000
  have h449024 := Scan.chunk_sound context_valid facts instructions 448512 512
    h448512 checked_448512
  have h449536 := Scan.chunk_sound context_valid facts instructions 449024 512
    h449024 checked_449024
  have h450048 := Scan.chunk_sound context_valid facts instructions 449536 512
    h449536 checked_449536
  have h450560 := Scan.chunk_sound context_valid facts instructions 450048 512
    h450048 checked_450048
  have h451072 := Scan.chunk_sound context_valid facts instructions 450560 512
    h450560 checked_450560
  have h451584 := Scan.chunk_sound context_valid facts instructions 451072 512
    h451072 checked_451072
  have h452096 := Scan.chunk_sound context_valid facts instructions 451584 512
    h451584 checked_451584
  have h452608 := Scan.chunk_sound context_valid facts instructions 452096 512
    h452096 checked_452096
  have h453120 := Scan.chunk_sound context_valid facts instructions 452608 512
    h452608 checked_452608
  have h453632 := Scan.chunk_sound context_valid facts instructions 453120 512
    h453120 checked_453120
  have h454144 := Scan.chunk_sound context_valid facts instructions 453632 512
    h453632 checked_453632
  have h454656 := Scan.chunk_sound context_valid facts instructions 454144 512
    h454144 checked_454144
  have h455168 := Scan.chunk_sound context_valid facts instructions 454656 512
    h454656 checked_454656
  have h455680 := Scan.chunk_sound context_valid facts instructions 455168 512
    h455168 checked_455168
  have h456192 := Scan.chunk_sound context_valid facts instructions 455680 512
    h455680 checked_455680
  have h456704 := Scan.chunk_sound context_valid facts instructions 456192 512
    h456192 checked_456192
  have h457216 := Scan.chunk_sound context_valid facts instructions 456704 512
    h456704 checked_456704
  have h457728 := Scan.chunk_sound context_valid facts instructions 457216 512
    h457216 checked_457216
  have h458240 := Scan.chunk_sound context_valid facts instructions 457728 512
    h457728 checked_457728
  have h458752 := Scan.chunk_sound context_valid facts instructions 458240 512
    h458240 checked_458240
  exact h458752

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCertificate
