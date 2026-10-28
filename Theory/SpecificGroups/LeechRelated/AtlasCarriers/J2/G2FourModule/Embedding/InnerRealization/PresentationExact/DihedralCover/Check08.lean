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
theorem checked_131072 : Scan.checkChunk context facts instructions 131072 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_131584 : Scan.checkChunk context facts instructions 131584 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_132096 : Scan.checkChunk context facts instructions 132096 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_132608 : Scan.checkChunk context facts instructions 132608 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_133120 : Scan.checkChunk context facts instructions 133120 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_133632 : Scan.checkChunk context facts instructions 133632 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_134144 : Scan.checkChunk context facts instructions 134144 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_134656 : Scan.checkChunk context facts instructions 134656 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_135168 : Scan.checkChunk context facts instructions 135168 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_135680 : Scan.checkChunk context facts instructions 135680 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_136192 : Scan.checkChunk context facts instructions 136192 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_136704 : Scan.checkChunk context facts instructions 136704 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_137216 : Scan.checkChunk context facts instructions 137216 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_137728 : Scan.checkChunk context facts instructions 137728 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_138240 : Scan.checkChunk context facts instructions 138240 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_138752 : Scan.checkChunk context facts instructions 138752 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_139264 : Scan.checkChunk context facts instructions 139264 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_139776 : Scan.checkChunk context facts instructions 139776 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_140288 : Scan.checkChunk context facts instructions 140288 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_140800 : Scan.checkChunk context facts instructions 140800 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_141312 : Scan.checkChunk context facts instructions 141312 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_141824 : Scan.checkChunk context facts instructions 141824 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_142336 : Scan.checkChunk context facts instructions 142336 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_142848 : Scan.checkChunk context facts instructions 142848 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_143360 : Scan.checkChunk context facts instructions 143360 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_143872 : Scan.checkChunk context facts instructions 143872 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_144384 : Scan.checkChunk context facts instructions 144384 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_144896 : Scan.checkChunk context facts instructions 144896 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_145408 : Scan.checkChunk context facts instructions 145408 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_145920 : Scan.checkChunk context facts instructions 145920 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_146432 : Scan.checkChunk context facts instructions 146432 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_146944 : Scan.checkChunk context facts instructions 146944 512 = true := by
  decide +kernel

theorem sound_131072 (prior : ∀ n, n < 131072 →
    Holds dihedral generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 147456 → Holds dihedral generator (definitions.repr generator) (facts n) := by
  have h131584 := Scan.chunk_sound context_valid facts instructions 131072 512
    prior checked_131072
  have h132096 := Scan.chunk_sound context_valid facts instructions 131584 512
    h131584 checked_131584
  have h132608 := Scan.chunk_sound context_valid facts instructions 132096 512
    h132096 checked_132096
  have h133120 := Scan.chunk_sound context_valid facts instructions 132608 512
    h132608 checked_132608
  have h133632 := Scan.chunk_sound context_valid facts instructions 133120 512
    h133120 checked_133120
  have h134144 := Scan.chunk_sound context_valid facts instructions 133632 512
    h133632 checked_133632
  have h134656 := Scan.chunk_sound context_valid facts instructions 134144 512
    h134144 checked_134144
  have h135168 := Scan.chunk_sound context_valid facts instructions 134656 512
    h134656 checked_134656
  have h135680 := Scan.chunk_sound context_valid facts instructions 135168 512
    h135168 checked_135168
  have h136192 := Scan.chunk_sound context_valid facts instructions 135680 512
    h135680 checked_135680
  have h136704 := Scan.chunk_sound context_valid facts instructions 136192 512
    h136192 checked_136192
  have h137216 := Scan.chunk_sound context_valid facts instructions 136704 512
    h136704 checked_136704
  have h137728 := Scan.chunk_sound context_valid facts instructions 137216 512
    h137216 checked_137216
  have h138240 := Scan.chunk_sound context_valid facts instructions 137728 512
    h137728 checked_137728
  have h138752 := Scan.chunk_sound context_valid facts instructions 138240 512
    h138240 checked_138240
  have h139264 := Scan.chunk_sound context_valid facts instructions 138752 512
    h138752 checked_138752
  have h139776 := Scan.chunk_sound context_valid facts instructions 139264 512
    h139264 checked_139264
  have h140288 := Scan.chunk_sound context_valid facts instructions 139776 512
    h139776 checked_139776
  have h140800 := Scan.chunk_sound context_valid facts instructions 140288 512
    h140288 checked_140288
  have h141312 := Scan.chunk_sound context_valid facts instructions 140800 512
    h140800 checked_140800
  have h141824 := Scan.chunk_sound context_valid facts instructions 141312 512
    h141312 checked_141312
  have h142336 := Scan.chunk_sound context_valid facts instructions 141824 512
    h141824 checked_141824
  have h142848 := Scan.chunk_sound context_valid facts instructions 142336 512
    h142336 checked_142336
  have h143360 := Scan.chunk_sound context_valid facts instructions 142848 512
    h142848 checked_142848
  have h143872 := Scan.chunk_sound context_valid facts instructions 143360 512
    h143360 checked_143360
  have h144384 := Scan.chunk_sound context_valid facts instructions 143872 512
    h143872 checked_143872
  have h144896 := Scan.chunk_sound context_valid facts instructions 144384 512
    h144384 checked_144384
  have h145408 := Scan.chunk_sound context_valid facts instructions 144896 512
    h144896 checked_144896
  have h145920 := Scan.chunk_sound context_valid facts instructions 145408 512
    h145408 checked_145408
  have h146432 := Scan.chunk_sound context_valid facts instructions 145920 512
    h145920 checked_145920
  have h146944 := Scan.chunk_sound context_valid facts instructions 146432 512
    h146432 checked_146432
  have h147456 := Scan.chunk_sound context_valid facts instructions 146944 512
    h146944 checked_146944
  exact h147456

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCertificate
