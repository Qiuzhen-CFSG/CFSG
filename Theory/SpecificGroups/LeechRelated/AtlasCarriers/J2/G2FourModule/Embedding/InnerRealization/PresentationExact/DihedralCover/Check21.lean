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
theorem checked_344064 : Scan.checkChunk context facts instructions 344064 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_344576 : Scan.checkChunk context facts instructions 344576 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_345088 : Scan.checkChunk context facts instructions 345088 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_345600 : Scan.checkChunk context facts instructions 345600 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_346112 : Scan.checkChunk context facts instructions 346112 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_346624 : Scan.checkChunk context facts instructions 346624 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_347136 : Scan.checkChunk context facts instructions 347136 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_347648 : Scan.checkChunk context facts instructions 347648 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_348160 : Scan.checkChunk context facts instructions 348160 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_348672 : Scan.checkChunk context facts instructions 348672 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_349184 : Scan.checkChunk context facts instructions 349184 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_349696 : Scan.checkChunk context facts instructions 349696 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_350208 : Scan.checkChunk context facts instructions 350208 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_350720 : Scan.checkChunk context facts instructions 350720 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_351232 : Scan.checkChunk context facts instructions 351232 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_351744 : Scan.checkChunk context facts instructions 351744 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_352256 : Scan.checkChunk context facts instructions 352256 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_352768 : Scan.checkChunk context facts instructions 352768 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_353280 : Scan.checkChunk context facts instructions 353280 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_353792 : Scan.checkChunk context facts instructions 353792 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_354304 : Scan.checkChunk context facts instructions 354304 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_354816 : Scan.checkChunk context facts instructions 354816 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_355328 : Scan.checkChunk context facts instructions 355328 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_355840 : Scan.checkChunk context facts instructions 355840 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_356352 : Scan.checkChunk context facts instructions 356352 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_356864 : Scan.checkChunk context facts instructions 356864 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_357376 : Scan.checkChunk context facts instructions 357376 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_357888 : Scan.checkChunk context facts instructions 357888 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_358400 : Scan.checkChunk context facts instructions 358400 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_358912 : Scan.checkChunk context facts instructions 358912 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_359424 : Scan.checkChunk context facts instructions 359424 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_359936 : Scan.checkChunk context facts instructions 359936 512 = true := by
  decide +kernel

theorem sound_344064 (prior : ∀ n, n < 344064 →
    Holds dihedral generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 360448 → Holds dihedral generator (definitions.repr generator) (facts n) := by
  have h344576 := Scan.chunk_sound context_valid facts instructions 344064 512
    prior checked_344064
  have h345088 := Scan.chunk_sound context_valid facts instructions 344576 512
    h344576 checked_344576
  have h345600 := Scan.chunk_sound context_valid facts instructions 345088 512
    h345088 checked_345088
  have h346112 := Scan.chunk_sound context_valid facts instructions 345600 512
    h345600 checked_345600
  have h346624 := Scan.chunk_sound context_valid facts instructions 346112 512
    h346112 checked_346112
  have h347136 := Scan.chunk_sound context_valid facts instructions 346624 512
    h346624 checked_346624
  have h347648 := Scan.chunk_sound context_valid facts instructions 347136 512
    h347136 checked_347136
  have h348160 := Scan.chunk_sound context_valid facts instructions 347648 512
    h347648 checked_347648
  have h348672 := Scan.chunk_sound context_valid facts instructions 348160 512
    h348160 checked_348160
  have h349184 := Scan.chunk_sound context_valid facts instructions 348672 512
    h348672 checked_348672
  have h349696 := Scan.chunk_sound context_valid facts instructions 349184 512
    h349184 checked_349184
  have h350208 := Scan.chunk_sound context_valid facts instructions 349696 512
    h349696 checked_349696
  have h350720 := Scan.chunk_sound context_valid facts instructions 350208 512
    h350208 checked_350208
  have h351232 := Scan.chunk_sound context_valid facts instructions 350720 512
    h350720 checked_350720
  have h351744 := Scan.chunk_sound context_valid facts instructions 351232 512
    h351232 checked_351232
  have h352256 := Scan.chunk_sound context_valid facts instructions 351744 512
    h351744 checked_351744
  have h352768 := Scan.chunk_sound context_valid facts instructions 352256 512
    h352256 checked_352256
  have h353280 := Scan.chunk_sound context_valid facts instructions 352768 512
    h352768 checked_352768
  have h353792 := Scan.chunk_sound context_valid facts instructions 353280 512
    h353280 checked_353280
  have h354304 := Scan.chunk_sound context_valid facts instructions 353792 512
    h353792 checked_353792
  have h354816 := Scan.chunk_sound context_valid facts instructions 354304 512
    h354304 checked_354304
  have h355328 := Scan.chunk_sound context_valid facts instructions 354816 512
    h354816 checked_354816
  have h355840 := Scan.chunk_sound context_valid facts instructions 355328 512
    h355328 checked_355328
  have h356352 := Scan.chunk_sound context_valid facts instructions 355840 512
    h355840 checked_355840
  have h356864 := Scan.chunk_sound context_valid facts instructions 356352 512
    h356352 checked_356352
  have h357376 := Scan.chunk_sound context_valid facts instructions 356864 512
    h356864 checked_356864
  have h357888 := Scan.chunk_sound context_valid facts instructions 357376 512
    h357376 checked_357376
  have h358400 := Scan.chunk_sound context_valid facts instructions 357888 512
    h357888 checked_357888
  have h358912 := Scan.chunk_sound context_valid facts instructions 358400 512
    h358400 checked_358400
  have h359424 := Scan.chunk_sound context_valid facts instructions 358912 512
    h358912 checked_358912
  have h359936 := Scan.chunk_sound context_valid facts instructions 359424 512
    h359424 checked_359424
  have h360448 := Scan.chunk_sound context_valid facts instructions 359936 512
    h359936 checked_359936
  exact h360448

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCertificate
