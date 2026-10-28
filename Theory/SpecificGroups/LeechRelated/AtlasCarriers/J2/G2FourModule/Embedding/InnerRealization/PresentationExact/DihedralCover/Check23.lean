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
theorem checked_376832 : Scan.checkChunk context facts instructions 376832 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_377344 : Scan.checkChunk context facts instructions 377344 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_377856 : Scan.checkChunk context facts instructions 377856 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_378368 : Scan.checkChunk context facts instructions 378368 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_378880 : Scan.checkChunk context facts instructions 378880 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_379392 : Scan.checkChunk context facts instructions 379392 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_379904 : Scan.checkChunk context facts instructions 379904 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_380416 : Scan.checkChunk context facts instructions 380416 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_380928 : Scan.checkChunk context facts instructions 380928 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_381440 : Scan.checkChunk context facts instructions 381440 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_381952 : Scan.checkChunk context facts instructions 381952 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_382464 : Scan.checkChunk context facts instructions 382464 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_382976 : Scan.checkChunk context facts instructions 382976 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_383488 : Scan.checkChunk context facts instructions 383488 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_384000 : Scan.checkChunk context facts instructions 384000 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_384512 : Scan.checkChunk context facts instructions 384512 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_385024 : Scan.checkChunk context facts instructions 385024 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_385536 : Scan.checkChunk context facts instructions 385536 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_386048 : Scan.checkChunk context facts instructions 386048 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_386560 : Scan.checkChunk context facts instructions 386560 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_387072 : Scan.checkChunk context facts instructions 387072 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_387584 : Scan.checkChunk context facts instructions 387584 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_388096 : Scan.checkChunk context facts instructions 388096 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_388608 : Scan.checkChunk context facts instructions 388608 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_389120 : Scan.checkChunk context facts instructions 389120 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_389632 : Scan.checkChunk context facts instructions 389632 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_390144 : Scan.checkChunk context facts instructions 390144 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_390656 : Scan.checkChunk context facts instructions 390656 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_391168 : Scan.checkChunk context facts instructions 391168 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_391680 : Scan.checkChunk context facts instructions 391680 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_392192 : Scan.checkChunk context facts instructions 392192 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_392704 : Scan.checkChunk context facts instructions 392704 512 = true := by
  decide +kernel

theorem sound_376832 (prior : ∀ n, n < 376832 →
    Holds dihedral generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 393216 → Holds dihedral generator (definitions.repr generator) (facts n) := by
  have h377344 := Scan.chunk_sound context_valid facts instructions 376832 512
    prior checked_376832
  have h377856 := Scan.chunk_sound context_valid facts instructions 377344 512
    h377344 checked_377344
  have h378368 := Scan.chunk_sound context_valid facts instructions 377856 512
    h377856 checked_377856
  have h378880 := Scan.chunk_sound context_valid facts instructions 378368 512
    h378368 checked_378368
  have h379392 := Scan.chunk_sound context_valid facts instructions 378880 512
    h378880 checked_378880
  have h379904 := Scan.chunk_sound context_valid facts instructions 379392 512
    h379392 checked_379392
  have h380416 := Scan.chunk_sound context_valid facts instructions 379904 512
    h379904 checked_379904
  have h380928 := Scan.chunk_sound context_valid facts instructions 380416 512
    h380416 checked_380416
  have h381440 := Scan.chunk_sound context_valid facts instructions 380928 512
    h380928 checked_380928
  have h381952 := Scan.chunk_sound context_valid facts instructions 381440 512
    h381440 checked_381440
  have h382464 := Scan.chunk_sound context_valid facts instructions 381952 512
    h381952 checked_381952
  have h382976 := Scan.chunk_sound context_valid facts instructions 382464 512
    h382464 checked_382464
  have h383488 := Scan.chunk_sound context_valid facts instructions 382976 512
    h382976 checked_382976
  have h384000 := Scan.chunk_sound context_valid facts instructions 383488 512
    h383488 checked_383488
  have h384512 := Scan.chunk_sound context_valid facts instructions 384000 512
    h384000 checked_384000
  have h385024 := Scan.chunk_sound context_valid facts instructions 384512 512
    h384512 checked_384512
  have h385536 := Scan.chunk_sound context_valid facts instructions 385024 512
    h385024 checked_385024
  have h386048 := Scan.chunk_sound context_valid facts instructions 385536 512
    h385536 checked_385536
  have h386560 := Scan.chunk_sound context_valid facts instructions 386048 512
    h386048 checked_386048
  have h387072 := Scan.chunk_sound context_valid facts instructions 386560 512
    h386560 checked_386560
  have h387584 := Scan.chunk_sound context_valid facts instructions 387072 512
    h387072 checked_387072
  have h388096 := Scan.chunk_sound context_valid facts instructions 387584 512
    h387584 checked_387584
  have h388608 := Scan.chunk_sound context_valid facts instructions 388096 512
    h388096 checked_388096
  have h389120 := Scan.chunk_sound context_valid facts instructions 388608 512
    h388608 checked_388608
  have h389632 := Scan.chunk_sound context_valid facts instructions 389120 512
    h389120 checked_389120
  have h390144 := Scan.chunk_sound context_valid facts instructions 389632 512
    h389632 checked_389632
  have h390656 := Scan.chunk_sound context_valid facts instructions 390144 512
    h390144 checked_390144
  have h391168 := Scan.chunk_sound context_valid facts instructions 390656 512
    h390656 checked_390656
  have h391680 := Scan.chunk_sound context_valid facts instructions 391168 512
    h391168 checked_391168
  have h392192 := Scan.chunk_sound context_valid facts instructions 391680 512
    h391680 checked_391680
  have h392704 := Scan.chunk_sound context_valid facts instructions 392192 512
    h392192 checked_392192
  have h393216 := Scan.chunk_sound context_valid facts instructions 392704 512
    h392704 checked_392704
  exact h393216

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCertificate
