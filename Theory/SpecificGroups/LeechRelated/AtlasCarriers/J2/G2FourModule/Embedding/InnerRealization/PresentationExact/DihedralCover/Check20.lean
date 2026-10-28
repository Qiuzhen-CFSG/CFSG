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
theorem checked_327680 : Scan.checkChunk context facts instructions 327680 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_328192 : Scan.checkChunk context facts instructions 328192 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_328704 : Scan.checkChunk context facts instructions 328704 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_329216 : Scan.checkChunk context facts instructions 329216 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_329728 : Scan.checkChunk context facts instructions 329728 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_330240 : Scan.checkChunk context facts instructions 330240 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_330752 : Scan.checkChunk context facts instructions 330752 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_331264 : Scan.checkChunk context facts instructions 331264 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_331776 : Scan.checkChunk context facts instructions 331776 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_332288 : Scan.checkChunk context facts instructions 332288 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_332800 : Scan.checkChunk context facts instructions 332800 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_333312 : Scan.checkChunk context facts instructions 333312 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_333824 : Scan.checkChunk context facts instructions 333824 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_334336 : Scan.checkChunk context facts instructions 334336 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_334848 : Scan.checkChunk context facts instructions 334848 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_335360 : Scan.checkChunk context facts instructions 335360 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_335872 : Scan.checkChunk context facts instructions 335872 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_336384 : Scan.checkChunk context facts instructions 336384 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_336896 : Scan.checkChunk context facts instructions 336896 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_337408 : Scan.checkChunk context facts instructions 337408 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_337920 : Scan.checkChunk context facts instructions 337920 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_338432 : Scan.checkChunk context facts instructions 338432 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_338944 : Scan.checkChunk context facts instructions 338944 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_339456 : Scan.checkChunk context facts instructions 339456 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_339968 : Scan.checkChunk context facts instructions 339968 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_340480 : Scan.checkChunk context facts instructions 340480 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_340992 : Scan.checkChunk context facts instructions 340992 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_341504 : Scan.checkChunk context facts instructions 341504 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_342016 : Scan.checkChunk context facts instructions 342016 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_342528 : Scan.checkChunk context facts instructions 342528 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_343040 : Scan.checkChunk context facts instructions 343040 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_343552 : Scan.checkChunk context facts instructions 343552 512 = true := by
  decide +kernel

theorem sound_327680 (prior : ∀ n, n < 327680 →
    Holds dihedral generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 344064 → Holds dihedral generator (definitions.repr generator) (facts n) := by
  have h328192 := Scan.chunk_sound context_valid facts instructions 327680 512
    prior checked_327680
  have h328704 := Scan.chunk_sound context_valid facts instructions 328192 512
    h328192 checked_328192
  have h329216 := Scan.chunk_sound context_valid facts instructions 328704 512
    h328704 checked_328704
  have h329728 := Scan.chunk_sound context_valid facts instructions 329216 512
    h329216 checked_329216
  have h330240 := Scan.chunk_sound context_valid facts instructions 329728 512
    h329728 checked_329728
  have h330752 := Scan.chunk_sound context_valid facts instructions 330240 512
    h330240 checked_330240
  have h331264 := Scan.chunk_sound context_valid facts instructions 330752 512
    h330752 checked_330752
  have h331776 := Scan.chunk_sound context_valid facts instructions 331264 512
    h331264 checked_331264
  have h332288 := Scan.chunk_sound context_valid facts instructions 331776 512
    h331776 checked_331776
  have h332800 := Scan.chunk_sound context_valid facts instructions 332288 512
    h332288 checked_332288
  have h333312 := Scan.chunk_sound context_valid facts instructions 332800 512
    h332800 checked_332800
  have h333824 := Scan.chunk_sound context_valid facts instructions 333312 512
    h333312 checked_333312
  have h334336 := Scan.chunk_sound context_valid facts instructions 333824 512
    h333824 checked_333824
  have h334848 := Scan.chunk_sound context_valid facts instructions 334336 512
    h334336 checked_334336
  have h335360 := Scan.chunk_sound context_valid facts instructions 334848 512
    h334848 checked_334848
  have h335872 := Scan.chunk_sound context_valid facts instructions 335360 512
    h335360 checked_335360
  have h336384 := Scan.chunk_sound context_valid facts instructions 335872 512
    h335872 checked_335872
  have h336896 := Scan.chunk_sound context_valid facts instructions 336384 512
    h336384 checked_336384
  have h337408 := Scan.chunk_sound context_valid facts instructions 336896 512
    h336896 checked_336896
  have h337920 := Scan.chunk_sound context_valid facts instructions 337408 512
    h337408 checked_337408
  have h338432 := Scan.chunk_sound context_valid facts instructions 337920 512
    h337920 checked_337920
  have h338944 := Scan.chunk_sound context_valid facts instructions 338432 512
    h338432 checked_338432
  have h339456 := Scan.chunk_sound context_valid facts instructions 338944 512
    h338944 checked_338944
  have h339968 := Scan.chunk_sound context_valid facts instructions 339456 512
    h339456 checked_339456
  have h340480 := Scan.chunk_sound context_valid facts instructions 339968 512
    h339968 checked_339968
  have h340992 := Scan.chunk_sound context_valid facts instructions 340480 512
    h340480 checked_340480
  have h341504 := Scan.chunk_sound context_valid facts instructions 340992 512
    h340992 checked_340992
  have h342016 := Scan.chunk_sound context_valid facts instructions 341504 512
    h341504 checked_341504
  have h342528 := Scan.chunk_sound context_valid facts instructions 342016 512
    h342016 checked_342016
  have h343040 := Scan.chunk_sound context_valid facts instructions 342528 512
    h342528 checked_342528
  have h343552 := Scan.chunk_sound context_valid facts instructions 343040 512
    h343040 checked_343040
  have h344064 := Scan.chunk_sound context_valid facts instructions 343552 512
    h343552 checked_343552
  exact h344064

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCertificate
