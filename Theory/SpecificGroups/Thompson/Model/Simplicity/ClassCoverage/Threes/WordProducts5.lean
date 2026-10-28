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
private theorem rC2_check : ∀ i : Fin 248,
    BinaryMatrix.rowProduct rCRows[i.val]! rCRows 248 = rC2Rows[i.val]! := by
  decide +kernel

 theorem rC2_product : BinaryMatrix.decode 248 rCRows *
    BinaryMatrix.decode 248 rCRows = BinaryMatrix.decode 248 rC2Rows :=
  BinaryMatrix.decode_mul 248 rCRows rCRows rC2Rows rC2_check

set_option maxHeartbeats 4000000 in
private theorem rC3_check : ∀ i : Fin 248,
    BinaryMatrix.rowProduct rC2Rows[i.val]! rCRows 248 = 2 ^ i.val := by
  decide +kernel

 theorem rC3_product : BinaryMatrix.decode 248 rC2Rows *
    BinaryMatrix.decode 248 rCRows = 1 :=
  BinaryMatrix.decode_mul_one 248 rC2Rows rCRows rC3_check

end Thompson.Simplicity.ThreeWordCertificate
