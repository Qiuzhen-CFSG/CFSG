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
private theorem c0_check : ∀ i : Fin 248,
    BinaryMatrix.rowProduct atlasARows[i.val]! vInvRows 248 = c0Rows[i.val]! := by
  decide +kernel

 theorem c0_product : BinaryMatrix.decode 248 atlasARows *
    BinaryMatrix.decode 248 vInvRows = BinaryMatrix.decode 248 c0Rows :=
  BinaryMatrix.decode_mul 248 atlasARows vInvRows c0Rows c0_check

set_option maxHeartbeats 4000000 in
private theorem c1_check : ∀ i : Fin 248,
    BinaryMatrix.rowProduct c0Rows[i.val]! atlasARows 248 = c1Rows[i.val]! := by
  decide +kernel

 theorem c1_product : BinaryMatrix.decode 248 c0Rows *
    BinaryMatrix.decode 248 atlasARows = BinaryMatrix.decode 248 c1Rows :=
  BinaryMatrix.decode_mul 248 c0Rows atlasARows c1Rows c1_check

set_option maxHeartbeats 4000000 in
private theorem c_check : ∀ i : Fin 248,
    BinaryMatrix.rowProduct c1Rows[i.val]! vRows 248 = cRows[i.val]! := by
  decide +kernel

 theorem c_product : BinaryMatrix.decode 248 c1Rows *
    BinaryMatrix.decode 248 vRows = BinaryMatrix.decode 248 cRows :=
  BinaryMatrix.decode_mul 248 c1Rows vRows cRows c_check

set_option maxHeartbeats 4000000 in
private theorem rC_check : ∀ i : Fin 248,
    BinaryMatrix.rowProduct cRows[i.val]! cRows 248 = rCRows[i.val]! := by
  decide +kernel

 theorem rC_product : BinaryMatrix.decode 248 cRows *
    BinaryMatrix.decode 248 cRows = BinaryMatrix.decode 248 rCRows :=
  BinaryMatrix.decode_mul 248 cRows cRows rCRows rC_check

end Thompson.Simplicity.ThreeWordCertificate
