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
theorem checked_114688 : Scan.checkChunk context facts instructions 114688 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_115200 : Scan.checkChunk context facts instructions 115200 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_115712 : Scan.checkChunk context facts instructions 115712 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_116224 : Scan.checkChunk context facts instructions 116224 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_116736 : Scan.checkChunk context facts instructions 116736 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_117248 : Scan.checkChunk context facts instructions 117248 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_117760 : Scan.checkChunk context facts instructions 117760 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_118272 : Scan.checkChunk context facts instructions 118272 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_118784 : Scan.checkChunk context facts instructions 118784 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_119296 : Scan.checkChunk context facts instructions 119296 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_119808 : Scan.checkChunk context facts instructions 119808 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_120320 : Scan.checkChunk context facts instructions 120320 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_120832 : Scan.checkChunk context facts instructions 120832 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_121344 : Scan.checkChunk context facts instructions 121344 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_121856 : Scan.checkChunk context facts instructions 121856 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_122368 : Scan.checkChunk context facts instructions 122368 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_122880 : Scan.checkChunk context facts instructions 122880 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_123392 : Scan.checkChunk context facts instructions 123392 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_123904 : Scan.checkChunk context facts instructions 123904 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_124416 : Scan.checkChunk context facts instructions 124416 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_124928 : Scan.checkChunk context facts instructions 124928 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_125440 : Scan.checkChunk context facts instructions 125440 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_125952 : Scan.checkChunk context facts instructions 125952 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_126464 : Scan.checkChunk context facts instructions 126464 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_126976 : Scan.checkChunk context facts instructions 126976 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_127488 : Scan.checkChunk context facts instructions 127488 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_128000 : Scan.checkChunk context facts instructions 128000 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_128512 : Scan.checkChunk context facts instructions 128512 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_129024 : Scan.checkChunk context facts instructions 129024 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_129536 : Scan.checkChunk context facts instructions 129536 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_130048 : Scan.checkChunk context facts instructions 130048 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_130560 : Scan.checkChunk context facts instructions 130560 512 = true := by
  decide +kernel

theorem sound_114688 (prior : ∀ n, n < 114688 →
    Holds dihedral generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 131072 → Holds dihedral generator (definitions.repr generator) (facts n) := by
  have h115200 := Scan.chunk_sound context_valid facts instructions 114688 512
    prior checked_114688
  have h115712 := Scan.chunk_sound context_valid facts instructions 115200 512
    h115200 checked_115200
  have h116224 := Scan.chunk_sound context_valid facts instructions 115712 512
    h115712 checked_115712
  have h116736 := Scan.chunk_sound context_valid facts instructions 116224 512
    h116224 checked_116224
  have h117248 := Scan.chunk_sound context_valid facts instructions 116736 512
    h116736 checked_116736
  have h117760 := Scan.chunk_sound context_valid facts instructions 117248 512
    h117248 checked_117248
  have h118272 := Scan.chunk_sound context_valid facts instructions 117760 512
    h117760 checked_117760
  have h118784 := Scan.chunk_sound context_valid facts instructions 118272 512
    h118272 checked_118272
  have h119296 := Scan.chunk_sound context_valid facts instructions 118784 512
    h118784 checked_118784
  have h119808 := Scan.chunk_sound context_valid facts instructions 119296 512
    h119296 checked_119296
  have h120320 := Scan.chunk_sound context_valid facts instructions 119808 512
    h119808 checked_119808
  have h120832 := Scan.chunk_sound context_valid facts instructions 120320 512
    h120320 checked_120320
  have h121344 := Scan.chunk_sound context_valid facts instructions 120832 512
    h120832 checked_120832
  have h121856 := Scan.chunk_sound context_valid facts instructions 121344 512
    h121344 checked_121344
  have h122368 := Scan.chunk_sound context_valid facts instructions 121856 512
    h121856 checked_121856
  have h122880 := Scan.chunk_sound context_valid facts instructions 122368 512
    h122368 checked_122368
  have h123392 := Scan.chunk_sound context_valid facts instructions 122880 512
    h122880 checked_122880
  have h123904 := Scan.chunk_sound context_valid facts instructions 123392 512
    h123392 checked_123392
  have h124416 := Scan.chunk_sound context_valid facts instructions 123904 512
    h123904 checked_123904
  have h124928 := Scan.chunk_sound context_valid facts instructions 124416 512
    h124416 checked_124416
  have h125440 := Scan.chunk_sound context_valid facts instructions 124928 512
    h124928 checked_124928
  have h125952 := Scan.chunk_sound context_valid facts instructions 125440 512
    h125440 checked_125440
  have h126464 := Scan.chunk_sound context_valid facts instructions 125952 512
    h125952 checked_125952
  have h126976 := Scan.chunk_sound context_valid facts instructions 126464 512
    h126464 checked_126464
  have h127488 := Scan.chunk_sound context_valid facts instructions 126976 512
    h126976 checked_126976
  have h128000 := Scan.chunk_sound context_valid facts instructions 127488 512
    h127488 checked_127488
  have h128512 := Scan.chunk_sound context_valid facts instructions 128000 512
    h128000 checked_128000
  have h129024 := Scan.chunk_sound context_valid facts instructions 128512 512
    h128512 checked_128512
  have h129536 := Scan.chunk_sound context_valid facts instructions 129024 512
    h129024 checked_129024
  have h130048 := Scan.chunk_sound context_valid facts instructions 129536 512
    h129536 checked_129536
  have h130560 := Scan.chunk_sound context_valid facts instructions 130048 512
    h130048 checked_130048
  have h131072 := Scan.chunk_sound context_valid facts instructions 130560 512
    h130560 checked_130560
  exact h131072

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCertificate
