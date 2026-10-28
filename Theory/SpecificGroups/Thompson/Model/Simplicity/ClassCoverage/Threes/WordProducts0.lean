module

public import Theory.SpecificGroups.Thompson.Model.Simplicity.ClassCoverage.Threes.WordRows

/-!
# Concrete matrix products for the Thompson order-three words

These literal packed rows are witnesses, checked by `BinaryMatrix.decode_mul`.
The generation script and source attribution are in `Threes/source/`.
No external computation is used as a proof.
-/

@[expose] public section
namespace Thompson.Simplicity.ThreeWordCertificate
set_option maxRecDepth 10000

set_option maxHeartbeats 4000000 in
private theorem b2_check : ∀ i : Fin 248,
    BinaryMatrix.rowProduct atlasBRows[i.val]! atlasBRows 248 = b2Rows[i.val]! := by
  decide +kernel

 theorem b2_product : BinaryMatrix.decode 248 atlasBRows *
    BinaryMatrix.decode 248 atlasBRows = BinaryMatrix.decode 248 b2Rows :=
  BinaryMatrix.decode_mul 248 atlasBRows atlasBRows b2Rows b2_check

set_option maxHeartbeats 4000000 in
private theorem ab_check : ∀ i : Fin 248,
    BinaryMatrix.rowProduct atlasARows[i.val]! atlasBRows 248 = abRows[i.val]! := by
  decide +kernel

 theorem ab_product : BinaryMatrix.decode 248 atlasARows *
    BinaryMatrix.decode 248 atlasBRows = BinaryMatrix.decode 248 abRows :=
  BinaryMatrix.decode_mul 248 atlasARows atlasBRows abRows ab_check

set_option maxHeartbeats 4000000 in
private theorem ab2_check : ∀ i : Fin 248,
    BinaryMatrix.rowProduct atlasARows[i.val]! b2Rows 248 = ab2Rows[i.val]! := by
  decide +kernel

 theorem ab2_product : BinaryMatrix.decode 248 atlasARows *
    BinaryMatrix.decode 248 b2Rows = BinaryMatrix.decode 248 ab2Rows :=
  BinaryMatrix.decode_mul 248 atlasARows b2Rows ab2Rows ab2_check

set_option maxHeartbeats 4000000 in
private theorem abab_check : ∀ i : Fin 248,
    BinaryMatrix.rowProduct abRows[i.val]! abRows 248 = ababRows[i.val]! := by
  decide +kernel

 theorem abab_product : BinaryMatrix.decode 248 abRows *
    BinaryMatrix.decode 248 abRows = BinaryMatrix.decode 248 ababRows :=
  BinaryMatrix.decode_mul 248 abRows abRows ababRows abab_check

end Thompson.Simplicity.ThreeWordCertificate
