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
theorem checked_425984 : Scan.checkChunk context facts instructions 425984 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_426496 : Scan.checkChunk context facts instructions 426496 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_427008 : Scan.checkChunk context facts instructions 427008 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_427520 : Scan.checkChunk context facts instructions 427520 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_428032 : Scan.checkChunk context facts instructions 428032 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_428544 : Scan.checkChunk context facts instructions 428544 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_429056 : Scan.checkChunk context facts instructions 429056 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_429568 : Scan.checkChunk context facts instructions 429568 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_430080 : Scan.checkChunk context facts instructions 430080 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_430592 : Scan.checkChunk context facts instructions 430592 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_431104 : Scan.checkChunk context facts instructions 431104 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_431616 : Scan.checkChunk context facts instructions 431616 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_432128 : Scan.checkChunk context facts instructions 432128 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_432640 : Scan.checkChunk context facts instructions 432640 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_433152 : Scan.checkChunk context facts instructions 433152 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_433664 : Scan.checkChunk context facts instructions 433664 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_434176 : Scan.checkChunk context facts instructions 434176 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_434688 : Scan.checkChunk context facts instructions 434688 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_435200 : Scan.checkChunk context facts instructions 435200 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_435712 : Scan.checkChunk context facts instructions 435712 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_436224 : Scan.checkChunk context facts instructions 436224 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_436736 : Scan.checkChunk context facts instructions 436736 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_437248 : Scan.checkChunk context facts instructions 437248 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_437760 : Scan.checkChunk context facts instructions 437760 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_438272 : Scan.checkChunk context facts instructions 438272 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_438784 : Scan.checkChunk context facts instructions 438784 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_439296 : Scan.checkChunk context facts instructions 439296 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_439808 : Scan.checkChunk context facts instructions 439808 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_440320 : Scan.checkChunk context facts instructions 440320 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_440832 : Scan.checkChunk context facts instructions 440832 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_441344 : Scan.checkChunk context facts instructions 441344 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_441856 : Scan.checkChunk context facts instructions 441856 512 = true := by
  decide +kernel

theorem sound_425984 (prior : ∀ n, n < 425984 →
    Holds dihedral generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 442368 → Holds dihedral generator (definitions.repr generator) (facts n) := by
  have h426496 := Scan.chunk_sound context_valid facts instructions 425984 512
    prior checked_425984
  have h427008 := Scan.chunk_sound context_valid facts instructions 426496 512
    h426496 checked_426496
  have h427520 := Scan.chunk_sound context_valid facts instructions 427008 512
    h427008 checked_427008
  have h428032 := Scan.chunk_sound context_valid facts instructions 427520 512
    h427520 checked_427520
  have h428544 := Scan.chunk_sound context_valid facts instructions 428032 512
    h428032 checked_428032
  have h429056 := Scan.chunk_sound context_valid facts instructions 428544 512
    h428544 checked_428544
  have h429568 := Scan.chunk_sound context_valid facts instructions 429056 512
    h429056 checked_429056
  have h430080 := Scan.chunk_sound context_valid facts instructions 429568 512
    h429568 checked_429568
  have h430592 := Scan.chunk_sound context_valid facts instructions 430080 512
    h430080 checked_430080
  have h431104 := Scan.chunk_sound context_valid facts instructions 430592 512
    h430592 checked_430592
  have h431616 := Scan.chunk_sound context_valid facts instructions 431104 512
    h431104 checked_431104
  have h432128 := Scan.chunk_sound context_valid facts instructions 431616 512
    h431616 checked_431616
  have h432640 := Scan.chunk_sound context_valid facts instructions 432128 512
    h432128 checked_432128
  have h433152 := Scan.chunk_sound context_valid facts instructions 432640 512
    h432640 checked_432640
  have h433664 := Scan.chunk_sound context_valid facts instructions 433152 512
    h433152 checked_433152
  have h434176 := Scan.chunk_sound context_valid facts instructions 433664 512
    h433664 checked_433664
  have h434688 := Scan.chunk_sound context_valid facts instructions 434176 512
    h434176 checked_434176
  have h435200 := Scan.chunk_sound context_valid facts instructions 434688 512
    h434688 checked_434688
  have h435712 := Scan.chunk_sound context_valid facts instructions 435200 512
    h435200 checked_435200
  have h436224 := Scan.chunk_sound context_valid facts instructions 435712 512
    h435712 checked_435712
  have h436736 := Scan.chunk_sound context_valid facts instructions 436224 512
    h436224 checked_436224
  have h437248 := Scan.chunk_sound context_valid facts instructions 436736 512
    h436736 checked_436736
  have h437760 := Scan.chunk_sound context_valid facts instructions 437248 512
    h437248 checked_437248
  have h438272 := Scan.chunk_sound context_valid facts instructions 437760 512
    h437760 checked_437760
  have h438784 := Scan.chunk_sound context_valid facts instructions 438272 512
    h438272 checked_438272
  have h439296 := Scan.chunk_sound context_valid facts instructions 438784 512
    h438784 checked_438784
  have h439808 := Scan.chunk_sound context_valid facts instructions 439296 512
    h439296 checked_439296
  have h440320 := Scan.chunk_sound context_valid facts instructions 439808 512
    h439808 checked_439808
  have h440832 := Scan.chunk_sound context_valid facts instructions 440320 512
    h440320 checked_440320
  have h441344 := Scan.chunk_sound context_valid facts instructions 440832 512
    h440832 checked_440832
  have h441856 := Scan.chunk_sound context_valid facts instructions 441344 512
    h441344 checked_441344
  have h442368 := Scan.chunk_sound context_valid facts instructions 441856 512
    h441856 checked_441856
  exact h442368

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCertificate
