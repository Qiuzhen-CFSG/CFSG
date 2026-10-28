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
theorem checked_16384 : Scan.checkChunk context facts instructions 16384 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_16896 : Scan.checkChunk context facts instructions 16896 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_17408 : Scan.checkChunk context facts instructions 17408 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_17920 : Scan.checkChunk context facts instructions 17920 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_18432 : Scan.checkChunk context facts instructions 18432 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_18944 : Scan.checkChunk context facts instructions 18944 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_19456 : Scan.checkChunk context facts instructions 19456 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_19968 : Scan.checkChunk context facts instructions 19968 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_20480 : Scan.checkChunk context facts instructions 20480 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_20992 : Scan.checkChunk context facts instructions 20992 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_21504 : Scan.checkChunk context facts instructions 21504 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_22016 : Scan.checkChunk context facts instructions 22016 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_22528 : Scan.checkChunk context facts instructions 22528 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_23040 : Scan.checkChunk context facts instructions 23040 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_23552 : Scan.checkChunk context facts instructions 23552 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_24064 : Scan.checkChunk context facts instructions 24064 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_24576 : Scan.checkChunk context facts instructions 24576 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_25088 : Scan.checkChunk context facts instructions 25088 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_25600 : Scan.checkChunk context facts instructions 25600 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_26112 : Scan.checkChunk context facts instructions 26112 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_26624 : Scan.checkChunk context facts instructions 26624 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_27136 : Scan.checkChunk context facts instructions 27136 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_27648 : Scan.checkChunk context facts instructions 27648 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_28160 : Scan.checkChunk context facts instructions 28160 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_28672 : Scan.checkChunk context facts instructions 28672 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_29184 : Scan.checkChunk context facts instructions 29184 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_29696 : Scan.checkChunk context facts instructions 29696 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_30208 : Scan.checkChunk context facts instructions 30208 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_30720 : Scan.checkChunk context facts instructions 30720 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_31232 : Scan.checkChunk context facts instructions 31232 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_31744 : Scan.checkChunk context facts instructions 31744 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_32256 : Scan.checkChunk context facts instructions 32256 512 = true := by
  decide +kernel

theorem sound_16384 (prior : ∀ n, n < 16384 →
    Holds dihedral generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 32768 → Holds dihedral generator (definitions.repr generator) (facts n) := by
  have h16896 := Scan.chunk_sound context_valid facts instructions 16384 512
    prior checked_16384
  have h17408 := Scan.chunk_sound context_valid facts instructions 16896 512
    h16896 checked_16896
  have h17920 := Scan.chunk_sound context_valid facts instructions 17408 512
    h17408 checked_17408
  have h18432 := Scan.chunk_sound context_valid facts instructions 17920 512
    h17920 checked_17920
  have h18944 := Scan.chunk_sound context_valid facts instructions 18432 512
    h18432 checked_18432
  have h19456 := Scan.chunk_sound context_valid facts instructions 18944 512
    h18944 checked_18944
  have h19968 := Scan.chunk_sound context_valid facts instructions 19456 512
    h19456 checked_19456
  have h20480 := Scan.chunk_sound context_valid facts instructions 19968 512
    h19968 checked_19968
  have h20992 := Scan.chunk_sound context_valid facts instructions 20480 512
    h20480 checked_20480
  have h21504 := Scan.chunk_sound context_valid facts instructions 20992 512
    h20992 checked_20992
  have h22016 := Scan.chunk_sound context_valid facts instructions 21504 512
    h21504 checked_21504
  have h22528 := Scan.chunk_sound context_valid facts instructions 22016 512
    h22016 checked_22016
  have h23040 := Scan.chunk_sound context_valid facts instructions 22528 512
    h22528 checked_22528
  have h23552 := Scan.chunk_sound context_valid facts instructions 23040 512
    h23040 checked_23040
  have h24064 := Scan.chunk_sound context_valid facts instructions 23552 512
    h23552 checked_23552
  have h24576 := Scan.chunk_sound context_valid facts instructions 24064 512
    h24064 checked_24064
  have h25088 := Scan.chunk_sound context_valid facts instructions 24576 512
    h24576 checked_24576
  have h25600 := Scan.chunk_sound context_valid facts instructions 25088 512
    h25088 checked_25088
  have h26112 := Scan.chunk_sound context_valid facts instructions 25600 512
    h25600 checked_25600
  have h26624 := Scan.chunk_sound context_valid facts instructions 26112 512
    h26112 checked_26112
  have h27136 := Scan.chunk_sound context_valid facts instructions 26624 512
    h26624 checked_26624
  have h27648 := Scan.chunk_sound context_valid facts instructions 27136 512
    h27136 checked_27136
  have h28160 := Scan.chunk_sound context_valid facts instructions 27648 512
    h27648 checked_27648
  have h28672 := Scan.chunk_sound context_valid facts instructions 28160 512
    h28160 checked_28160
  have h29184 := Scan.chunk_sound context_valid facts instructions 28672 512
    h28672 checked_28672
  have h29696 := Scan.chunk_sound context_valid facts instructions 29184 512
    h29184 checked_29184
  have h30208 := Scan.chunk_sound context_valid facts instructions 29696 512
    h29696 checked_29696
  have h30720 := Scan.chunk_sound context_valid facts instructions 30208 512
    h30208 checked_30208
  have h31232 := Scan.chunk_sound context_valid facts instructions 30720 512
    h30720 checked_30720
  have h31744 := Scan.chunk_sound context_valid facts instructions 31232 512
    h31232 checked_31232
  have h32256 := Scan.chunk_sound context_valid facts instructions 31744 512
    h31744 checked_31744
  have h32768 := Scan.chunk_sound context_valid facts instructions 32256 512
    h32256 checked_32256
  exact h32768

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCertificate
