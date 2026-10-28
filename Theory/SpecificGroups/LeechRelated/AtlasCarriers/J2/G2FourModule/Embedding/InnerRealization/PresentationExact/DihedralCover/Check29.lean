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
theorem checked_475136 : Scan.checkChunk context facts instructions 475136 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_475648 : Scan.checkChunk context facts instructions 475648 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_476160 : Scan.checkChunk context facts instructions 476160 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_476672 : Scan.checkChunk context facts instructions 476672 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_477184 : Scan.checkChunk context facts instructions 477184 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_477696 : Scan.checkChunk context facts instructions 477696 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_478208 : Scan.checkChunk context facts instructions 478208 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_478720 : Scan.checkChunk context facts instructions 478720 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_479232 : Scan.checkChunk context facts instructions 479232 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_479744 : Scan.checkChunk context facts instructions 479744 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_480256 : Scan.checkChunk context facts instructions 480256 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_480768 : Scan.checkChunk context facts instructions 480768 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_481280 : Scan.checkChunk context facts instructions 481280 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_481792 : Scan.checkChunk context facts instructions 481792 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_482304 : Scan.checkChunk context facts instructions 482304 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_482816 : Scan.checkChunk context facts instructions 482816 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_483328 : Scan.checkChunk context facts instructions 483328 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_483840 : Scan.checkChunk context facts instructions 483840 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_484352 : Scan.checkChunk context facts instructions 484352 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_484864 : Scan.checkChunk context facts instructions 484864 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_485376 : Scan.checkChunk context facts instructions 485376 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_485888 : Scan.checkChunk context facts instructions 485888 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_486400 : Scan.checkChunk context facts instructions 486400 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_486912 : Scan.checkChunk context facts instructions 486912 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_487424 : Scan.checkChunk context facts instructions 487424 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_487936 : Scan.checkChunk context facts instructions 487936 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_488448 : Scan.checkChunk context facts instructions 488448 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_488960 : Scan.checkChunk context facts instructions 488960 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_489472 : Scan.checkChunk context facts instructions 489472 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_489984 : Scan.checkChunk context facts instructions 489984 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_490496 : Scan.checkChunk context facts instructions 490496 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_491008 : Scan.checkChunk context facts instructions 491008 512 = true := by
  decide +kernel

theorem sound_475136 (prior : ∀ n, n < 475136 →
    Holds dihedral generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 491520 → Holds dihedral generator (definitions.repr generator) (facts n) := by
  have h475648 := Scan.chunk_sound context_valid facts instructions 475136 512
    prior checked_475136
  have h476160 := Scan.chunk_sound context_valid facts instructions 475648 512
    h475648 checked_475648
  have h476672 := Scan.chunk_sound context_valid facts instructions 476160 512
    h476160 checked_476160
  have h477184 := Scan.chunk_sound context_valid facts instructions 476672 512
    h476672 checked_476672
  have h477696 := Scan.chunk_sound context_valid facts instructions 477184 512
    h477184 checked_477184
  have h478208 := Scan.chunk_sound context_valid facts instructions 477696 512
    h477696 checked_477696
  have h478720 := Scan.chunk_sound context_valid facts instructions 478208 512
    h478208 checked_478208
  have h479232 := Scan.chunk_sound context_valid facts instructions 478720 512
    h478720 checked_478720
  have h479744 := Scan.chunk_sound context_valid facts instructions 479232 512
    h479232 checked_479232
  have h480256 := Scan.chunk_sound context_valid facts instructions 479744 512
    h479744 checked_479744
  have h480768 := Scan.chunk_sound context_valid facts instructions 480256 512
    h480256 checked_480256
  have h481280 := Scan.chunk_sound context_valid facts instructions 480768 512
    h480768 checked_480768
  have h481792 := Scan.chunk_sound context_valid facts instructions 481280 512
    h481280 checked_481280
  have h482304 := Scan.chunk_sound context_valid facts instructions 481792 512
    h481792 checked_481792
  have h482816 := Scan.chunk_sound context_valid facts instructions 482304 512
    h482304 checked_482304
  have h483328 := Scan.chunk_sound context_valid facts instructions 482816 512
    h482816 checked_482816
  have h483840 := Scan.chunk_sound context_valid facts instructions 483328 512
    h483328 checked_483328
  have h484352 := Scan.chunk_sound context_valid facts instructions 483840 512
    h483840 checked_483840
  have h484864 := Scan.chunk_sound context_valid facts instructions 484352 512
    h484352 checked_484352
  have h485376 := Scan.chunk_sound context_valid facts instructions 484864 512
    h484864 checked_484864
  have h485888 := Scan.chunk_sound context_valid facts instructions 485376 512
    h485376 checked_485376
  have h486400 := Scan.chunk_sound context_valid facts instructions 485888 512
    h485888 checked_485888
  have h486912 := Scan.chunk_sound context_valid facts instructions 486400 512
    h486400 checked_486400
  have h487424 := Scan.chunk_sound context_valid facts instructions 486912 512
    h486912 checked_486912
  have h487936 := Scan.chunk_sound context_valid facts instructions 487424 512
    h487424 checked_487424
  have h488448 := Scan.chunk_sound context_valid facts instructions 487936 512
    h487936 checked_487936
  have h488960 := Scan.chunk_sound context_valid facts instructions 488448 512
    h488448 checked_488448
  have h489472 := Scan.chunk_sound context_valid facts instructions 488960 512
    h488960 checked_488960
  have h489984 := Scan.chunk_sound context_valid facts instructions 489472 512
    h489472 checked_489472
  have h490496 := Scan.chunk_sound context_valid facts instructions 489984 512
    h489984 checked_489984
  have h491008 := Scan.chunk_sound context_valid facts instructions 490496 512
    h490496 checked_490496
  have h491520 := Scan.chunk_sound context_valid facts instructions 491008 512
    h491008 checked_491008
  exact h491520

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCertificate
