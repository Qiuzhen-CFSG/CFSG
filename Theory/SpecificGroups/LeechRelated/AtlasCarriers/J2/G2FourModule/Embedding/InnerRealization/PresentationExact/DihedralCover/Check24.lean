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
theorem checked_393216 : Scan.checkChunk context facts instructions 393216 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_393728 : Scan.checkChunk context facts instructions 393728 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_394240 : Scan.checkChunk context facts instructions 394240 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_394752 : Scan.checkChunk context facts instructions 394752 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_395264 : Scan.checkChunk context facts instructions 395264 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_395776 : Scan.checkChunk context facts instructions 395776 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_396288 : Scan.checkChunk context facts instructions 396288 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_396800 : Scan.checkChunk context facts instructions 396800 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_397312 : Scan.checkChunk context facts instructions 397312 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_397824 : Scan.checkChunk context facts instructions 397824 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_398336 : Scan.checkChunk context facts instructions 398336 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_398848 : Scan.checkChunk context facts instructions 398848 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_399360 : Scan.checkChunk context facts instructions 399360 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_399872 : Scan.checkChunk context facts instructions 399872 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_400384 : Scan.checkChunk context facts instructions 400384 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_400896 : Scan.checkChunk context facts instructions 400896 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_401408 : Scan.checkChunk context facts instructions 401408 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_401920 : Scan.checkChunk context facts instructions 401920 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_402432 : Scan.checkChunk context facts instructions 402432 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_402944 : Scan.checkChunk context facts instructions 402944 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_403456 : Scan.checkChunk context facts instructions 403456 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_403968 : Scan.checkChunk context facts instructions 403968 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_404480 : Scan.checkChunk context facts instructions 404480 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_404992 : Scan.checkChunk context facts instructions 404992 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_405504 : Scan.checkChunk context facts instructions 405504 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_406016 : Scan.checkChunk context facts instructions 406016 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_406528 : Scan.checkChunk context facts instructions 406528 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_407040 : Scan.checkChunk context facts instructions 407040 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_407552 : Scan.checkChunk context facts instructions 407552 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_408064 : Scan.checkChunk context facts instructions 408064 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_408576 : Scan.checkChunk context facts instructions 408576 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_409088 : Scan.checkChunk context facts instructions 409088 512 = true := by
  decide +kernel

theorem sound_393216 (prior : ∀ n, n < 393216 →
    Holds dihedral generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 409600 → Holds dihedral generator (definitions.repr generator) (facts n) := by
  have h393728 := Scan.chunk_sound context_valid facts instructions 393216 512
    prior checked_393216
  have h394240 := Scan.chunk_sound context_valid facts instructions 393728 512
    h393728 checked_393728
  have h394752 := Scan.chunk_sound context_valid facts instructions 394240 512
    h394240 checked_394240
  have h395264 := Scan.chunk_sound context_valid facts instructions 394752 512
    h394752 checked_394752
  have h395776 := Scan.chunk_sound context_valid facts instructions 395264 512
    h395264 checked_395264
  have h396288 := Scan.chunk_sound context_valid facts instructions 395776 512
    h395776 checked_395776
  have h396800 := Scan.chunk_sound context_valid facts instructions 396288 512
    h396288 checked_396288
  have h397312 := Scan.chunk_sound context_valid facts instructions 396800 512
    h396800 checked_396800
  have h397824 := Scan.chunk_sound context_valid facts instructions 397312 512
    h397312 checked_397312
  have h398336 := Scan.chunk_sound context_valid facts instructions 397824 512
    h397824 checked_397824
  have h398848 := Scan.chunk_sound context_valid facts instructions 398336 512
    h398336 checked_398336
  have h399360 := Scan.chunk_sound context_valid facts instructions 398848 512
    h398848 checked_398848
  have h399872 := Scan.chunk_sound context_valid facts instructions 399360 512
    h399360 checked_399360
  have h400384 := Scan.chunk_sound context_valid facts instructions 399872 512
    h399872 checked_399872
  have h400896 := Scan.chunk_sound context_valid facts instructions 400384 512
    h400384 checked_400384
  have h401408 := Scan.chunk_sound context_valid facts instructions 400896 512
    h400896 checked_400896
  have h401920 := Scan.chunk_sound context_valid facts instructions 401408 512
    h401408 checked_401408
  have h402432 := Scan.chunk_sound context_valid facts instructions 401920 512
    h401920 checked_401920
  have h402944 := Scan.chunk_sound context_valid facts instructions 402432 512
    h402432 checked_402432
  have h403456 := Scan.chunk_sound context_valid facts instructions 402944 512
    h402944 checked_402944
  have h403968 := Scan.chunk_sound context_valid facts instructions 403456 512
    h403456 checked_403456
  have h404480 := Scan.chunk_sound context_valid facts instructions 403968 512
    h403968 checked_403968
  have h404992 := Scan.chunk_sound context_valid facts instructions 404480 512
    h404480 checked_404480
  have h405504 := Scan.chunk_sound context_valid facts instructions 404992 512
    h404992 checked_404992
  have h406016 := Scan.chunk_sound context_valid facts instructions 405504 512
    h405504 checked_405504
  have h406528 := Scan.chunk_sound context_valid facts instructions 406016 512
    h406016 checked_406016
  have h407040 := Scan.chunk_sound context_valid facts instructions 406528 512
    h406528 checked_406528
  have h407552 := Scan.chunk_sound context_valid facts instructions 407040 512
    h407040 checked_407040
  have h408064 := Scan.chunk_sound context_valid facts instructions 407552 512
    h407552 checked_407552
  have h408576 := Scan.chunk_sound context_valid facts instructions 408064 512
    h408064 checked_408064
  have h409088 := Scan.chunk_sound context_valid facts instructions 408576 512
    h408576 checked_408576
  have h409600 := Scan.chunk_sound context_valid facts instructions 409088 512
    h409088 checked_409088
  exact h409600

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCertificate
