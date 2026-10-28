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
private theorem rB2_check : ∀ i : Fin 248,
    BinaryMatrix.rowProduct rBRows[i.val]! rBRows 248 = rB2Rows[i.val]! := by
  decide +kernel

 theorem rB2_product : BinaryMatrix.decode 248 rBRows *
    BinaryMatrix.decode 248 rBRows = BinaryMatrix.decode 248 rB2Rows :=
  BinaryMatrix.decode_mul 248 rBRows rBRows rB2Rows rB2_check

set_option maxHeartbeats 4000000 in
private theorem rB3_check : ∀ i : Fin 248,
    BinaryMatrix.rowProduct rB2Rows[i.val]! rBRows 248 = 2 ^ i.val := by
  decide +kernel

 theorem rB3_product : BinaryMatrix.decode 248 rB2Rows *
    BinaryMatrix.decode 248 rBRows = 1 :=
  BinaryMatrix.decode_mul_one 248 rB2Rows rBRows rB3_check

set_option maxHeartbeats 4000000 in
private theorem b2a_check : ∀ i : Fin 248,
    BinaryMatrix.rowProduct b2Rows[i.val]! atlasARows 248 = b2aRows[i.val]! := by
  decide +kernel

 theorem b2a_product : BinaryMatrix.decode 248 b2Rows *
    BinaryMatrix.decode 248 atlasARows = BinaryMatrix.decode 248 b2aRows :=
  BinaryMatrix.decode_mul 248 b2Rows atlasARows b2aRows b2a_check

set_option maxHeartbeats 4000000 in
private theorem vInv0_check : ∀ i : Fin 248,
    BinaryMatrix.rowProduct b2aRows[i.val]! b2aRows 248 = vInv0Rows[i.val]! := by
  decide +kernel

 theorem vInv0_product : BinaryMatrix.decode 248 b2aRows *
    BinaryMatrix.decode 248 b2aRows = BinaryMatrix.decode 248 vInv0Rows :=
  BinaryMatrix.decode_mul 248 b2aRows b2aRows vInv0Rows vInv0_check

end Thompson.Simplicity.ThreeWordCertificate
