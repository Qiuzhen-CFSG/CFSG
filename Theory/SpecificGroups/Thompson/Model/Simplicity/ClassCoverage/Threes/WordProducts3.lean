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
private theorem vInv_check : ∀ i : Fin 248,
    BinaryMatrix.rowProduct vInv0Rows[i.val]! b2Rows 248 = vInvRows[i.val]! := by
  decide +kernel

 theorem vInv_product : BinaryMatrix.decode 248 vInv0Rows *
    BinaryMatrix.decode 248 b2Rows = BinaryMatrix.decode 248 vInvRows :=
  BinaryMatrix.decode_mul 248 vInv0Rows b2Rows vInvRows vInv_check

set_option maxHeartbeats 4000000 in
private theorem v0_check : ∀ i : Fin 248,
    BinaryMatrix.rowProduct atlasBRows[i.val]! atlasARows 248 = v0Rows[i.val]! := by
  decide +kernel

 theorem v0_product : BinaryMatrix.decode 248 atlasBRows *
    BinaryMatrix.decode 248 atlasARows = BinaryMatrix.decode 248 v0Rows :=
  BinaryMatrix.decode_mul 248 atlasBRows atlasARows v0Rows v0_check

set_option maxHeartbeats 4000000 in
private theorem v1_check : ∀ i : Fin 248,
    BinaryMatrix.rowProduct v0Rows[i.val]! v0Rows 248 = v1Rows[i.val]! := by
  decide +kernel

 theorem v1_product : BinaryMatrix.decode 248 v0Rows *
    BinaryMatrix.decode 248 v0Rows = BinaryMatrix.decode 248 v1Rows :=
  BinaryMatrix.decode_mul 248 v0Rows v0Rows v1Rows v1_check

set_option maxHeartbeats 4000000 in
private theorem v_check : ∀ i : Fin 248,
    BinaryMatrix.rowProduct v1Rows[i.val]! atlasBRows 248 = vRows[i.val]! := by
  decide +kernel

 theorem v_product : BinaryMatrix.decode 248 v1Rows *
    BinaryMatrix.decode 248 atlasBRows = BinaryMatrix.decode 248 vRows :=
  BinaryMatrix.decode_mul 248 v1Rows atlasBRows vRows v_check

end Thompson.Simplicity.ThreeWordCertificate
