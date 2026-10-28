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
theorem checked_180224 : Scan.checkChunk context facts instructions 180224 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_180736 : Scan.checkChunk context facts instructions 180736 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_181248 : Scan.checkChunk context facts instructions 181248 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_181760 : Scan.checkChunk context facts instructions 181760 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_182272 : Scan.checkChunk context facts instructions 182272 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_182784 : Scan.checkChunk context facts instructions 182784 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_183296 : Scan.checkChunk context facts instructions 183296 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_183808 : Scan.checkChunk context facts instructions 183808 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_184320 : Scan.checkChunk context facts instructions 184320 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_184832 : Scan.checkChunk context facts instructions 184832 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_185344 : Scan.checkChunk context facts instructions 185344 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_185856 : Scan.checkChunk context facts instructions 185856 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_186368 : Scan.checkChunk context facts instructions 186368 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_186880 : Scan.checkChunk context facts instructions 186880 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_187392 : Scan.checkChunk context facts instructions 187392 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_187904 : Scan.checkChunk context facts instructions 187904 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_188416 : Scan.checkChunk context facts instructions 188416 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_188928 : Scan.checkChunk context facts instructions 188928 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_189440 : Scan.checkChunk context facts instructions 189440 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_189952 : Scan.checkChunk context facts instructions 189952 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_190464 : Scan.checkChunk context facts instructions 190464 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_190976 : Scan.checkChunk context facts instructions 190976 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_191488 : Scan.checkChunk context facts instructions 191488 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_192000 : Scan.checkChunk context facts instructions 192000 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_192512 : Scan.checkChunk context facts instructions 192512 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_193024 : Scan.checkChunk context facts instructions 193024 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_193536 : Scan.checkChunk context facts instructions 193536 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_194048 : Scan.checkChunk context facts instructions 194048 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_194560 : Scan.checkChunk context facts instructions 194560 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_195072 : Scan.checkChunk context facts instructions 195072 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_195584 : Scan.checkChunk context facts instructions 195584 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_196096 : Scan.checkChunk context facts instructions 196096 512 = true := by
  decide +kernel

theorem sound_180224 (prior : ∀ n, n < 180224 →
    Holds dihedral generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 196608 → Holds dihedral generator (definitions.repr generator) (facts n) := by
  have h180736 := Scan.chunk_sound context_valid facts instructions 180224 512
    prior checked_180224
  have h181248 := Scan.chunk_sound context_valid facts instructions 180736 512
    h180736 checked_180736
  have h181760 := Scan.chunk_sound context_valid facts instructions 181248 512
    h181248 checked_181248
  have h182272 := Scan.chunk_sound context_valid facts instructions 181760 512
    h181760 checked_181760
  have h182784 := Scan.chunk_sound context_valid facts instructions 182272 512
    h182272 checked_182272
  have h183296 := Scan.chunk_sound context_valid facts instructions 182784 512
    h182784 checked_182784
  have h183808 := Scan.chunk_sound context_valid facts instructions 183296 512
    h183296 checked_183296
  have h184320 := Scan.chunk_sound context_valid facts instructions 183808 512
    h183808 checked_183808
  have h184832 := Scan.chunk_sound context_valid facts instructions 184320 512
    h184320 checked_184320
  have h185344 := Scan.chunk_sound context_valid facts instructions 184832 512
    h184832 checked_184832
  have h185856 := Scan.chunk_sound context_valid facts instructions 185344 512
    h185344 checked_185344
  have h186368 := Scan.chunk_sound context_valid facts instructions 185856 512
    h185856 checked_185856
  have h186880 := Scan.chunk_sound context_valid facts instructions 186368 512
    h186368 checked_186368
  have h187392 := Scan.chunk_sound context_valid facts instructions 186880 512
    h186880 checked_186880
  have h187904 := Scan.chunk_sound context_valid facts instructions 187392 512
    h187392 checked_187392
  have h188416 := Scan.chunk_sound context_valid facts instructions 187904 512
    h187904 checked_187904
  have h188928 := Scan.chunk_sound context_valid facts instructions 188416 512
    h188416 checked_188416
  have h189440 := Scan.chunk_sound context_valid facts instructions 188928 512
    h188928 checked_188928
  have h189952 := Scan.chunk_sound context_valid facts instructions 189440 512
    h189440 checked_189440
  have h190464 := Scan.chunk_sound context_valid facts instructions 189952 512
    h189952 checked_189952
  have h190976 := Scan.chunk_sound context_valid facts instructions 190464 512
    h190464 checked_190464
  have h191488 := Scan.chunk_sound context_valid facts instructions 190976 512
    h190976 checked_190976
  have h192000 := Scan.chunk_sound context_valid facts instructions 191488 512
    h191488 checked_191488
  have h192512 := Scan.chunk_sound context_valid facts instructions 192000 512
    h192000 checked_192000
  have h193024 := Scan.chunk_sound context_valid facts instructions 192512 512
    h192512 checked_192512
  have h193536 := Scan.chunk_sound context_valid facts instructions 193024 512
    h193024 checked_193024
  have h194048 := Scan.chunk_sound context_valid facts instructions 193536 512
    h193536 checked_193536
  have h194560 := Scan.chunk_sound context_valid facts instructions 194048 512
    h194048 checked_194048
  have h195072 := Scan.chunk_sound context_valid facts instructions 194560 512
    h194560 checked_194560
  have h195584 := Scan.chunk_sound context_valid facts instructions 195072 512
    h195072 checked_195072
  have h196096 := Scan.chunk_sound context_valid facts instructions 195584 512
    h195584 checked_195584
  have h196608 := Scan.chunk_sound context_valid facts instructions 196096 512
    h196096 checked_196096
  exact h196608

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCertificate
