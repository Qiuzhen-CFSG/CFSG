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
theorem checked_32768 : Scan.checkChunk context facts instructions 32768 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_33280 : Scan.checkChunk context facts instructions 33280 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_33792 : Scan.checkChunk context facts instructions 33792 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_34304 : Scan.checkChunk context facts instructions 34304 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_34816 : Scan.checkChunk context facts instructions 34816 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_35328 : Scan.checkChunk context facts instructions 35328 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_35840 : Scan.checkChunk context facts instructions 35840 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_36352 : Scan.checkChunk context facts instructions 36352 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_36864 : Scan.checkChunk context facts instructions 36864 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_37376 : Scan.checkChunk context facts instructions 37376 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_37888 : Scan.checkChunk context facts instructions 37888 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_38400 : Scan.checkChunk context facts instructions 38400 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_38912 : Scan.checkChunk context facts instructions 38912 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_39424 : Scan.checkChunk context facts instructions 39424 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_39936 : Scan.checkChunk context facts instructions 39936 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_40448 : Scan.checkChunk context facts instructions 40448 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_40960 : Scan.checkChunk context facts instructions 40960 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_41472 : Scan.checkChunk context facts instructions 41472 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_41984 : Scan.checkChunk context facts instructions 41984 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_42496 : Scan.checkChunk context facts instructions 42496 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_43008 : Scan.checkChunk context facts instructions 43008 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_43520 : Scan.checkChunk context facts instructions 43520 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_44032 : Scan.checkChunk context facts instructions 44032 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_44544 : Scan.checkChunk context facts instructions 44544 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_45056 : Scan.checkChunk context facts instructions 45056 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_45568 : Scan.checkChunk context facts instructions 45568 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_46080 : Scan.checkChunk context facts instructions 46080 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_46592 : Scan.checkChunk context facts instructions 46592 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_47104 : Scan.checkChunk context facts instructions 47104 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_47616 : Scan.checkChunk context facts instructions 47616 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_48128 : Scan.checkChunk context facts instructions 48128 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_48640 : Scan.checkChunk context facts instructions 48640 512 = true := by
  decide +kernel

theorem sound_32768 (prior : ∀ n, n < 32768 →
    Holds dihedral generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 49152 → Holds dihedral generator (definitions.repr generator) (facts n) := by
  have h33280 := Scan.chunk_sound context_valid facts instructions 32768 512
    prior checked_32768
  have h33792 := Scan.chunk_sound context_valid facts instructions 33280 512
    h33280 checked_33280
  have h34304 := Scan.chunk_sound context_valid facts instructions 33792 512
    h33792 checked_33792
  have h34816 := Scan.chunk_sound context_valid facts instructions 34304 512
    h34304 checked_34304
  have h35328 := Scan.chunk_sound context_valid facts instructions 34816 512
    h34816 checked_34816
  have h35840 := Scan.chunk_sound context_valid facts instructions 35328 512
    h35328 checked_35328
  have h36352 := Scan.chunk_sound context_valid facts instructions 35840 512
    h35840 checked_35840
  have h36864 := Scan.chunk_sound context_valid facts instructions 36352 512
    h36352 checked_36352
  have h37376 := Scan.chunk_sound context_valid facts instructions 36864 512
    h36864 checked_36864
  have h37888 := Scan.chunk_sound context_valid facts instructions 37376 512
    h37376 checked_37376
  have h38400 := Scan.chunk_sound context_valid facts instructions 37888 512
    h37888 checked_37888
  have h38912 := Scan.chunk_sound context_valid facts instructions 38400 512
    h38400 checked_38400
  have h39424 := Scan.chunk_sound context_valid facts instructions 38912 512
    h38912 checked_38912
  have h39936 := Scan.chunk_sound context_valid facts instructions 39424 512
    h39424 checked_39424
  have h40448 := Scan.chunk_sound context_valid facts instructions 39936 512
    h39936 checked_39936
  have h40960 := Scan.chunk_sound context_valid facts instructions 40448 512
    h40448 checked_40448
  have h41472 := Scan.chunk_sound context_valid facts instructions 40960 512
    h40960 checked_40960
  have h41984 := Scan.chunk_sound context_valid facts instructions 41472 512
    h41472 checked_41472
  have h42496 := Scan.chunk_sound context_valid facts instructions 41984 512
    h41984 checked_41984
  have h43008 := Scan.chunk_sound context_valid facts instructions 42496 512
    h42496 checked_42496
  have h43520 := Scan.chunk_sound context_valid facts instructions 43008 512
    h43008 checked_43008
  have h44032 := Scan.chunk_sound context_valid facts instructions 43520 512
    h43520 checked_43520
  have h44544 := Scan.chunk_sound context_valid facts instructions 44032 512
    h44032 checked_44032
  have h45056 := Scan.chunk_sound context_valid facts instructions 44544 512
    h44544 checked_44544
  have h45568 := Scan.chunk_sound context_valid facts instructions 45056 512
    h45056 checked_45056
  have h46080 := Scan.chunk_sound context_valid facts instructions 45568 512
    h45568 checked_45568
  have h46592 := Scan.chunk_sound context_valid facts instructions 46080 512
    h46080 checked_46080
  have h47104 := Scan.chunk_sound context_valid facts instructions 46592 512
    h46592 checked_46592
  have h47616 := Scan.chunk_sound context_valid facts instructions 47104 512
    h47104 checked_47104
  have h48128 := Scan.chunk_sound context_valid facts instructions 47616 512
    h47616 checked_47616
  have h48640 := Scan.chunk_sound context_valid facts instructions 48128 512
    h48128 checked_48128
  have h49152 := Scan.chunk_sound context_valid facts instructions 48640 512
    h48640 checked_48640
  exact h49152

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCertificate
