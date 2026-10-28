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
private theorem u_check : ∀ i : Fin 248,
    BinaryMatrix.rowProduct ababRows[i.val]! ab2Rows 248 = uRows[i.val]! := by
  decide +kernel

 theorem u_product : BinaryMatrix.decode 248 ababRows *
    BinaryMatrix.decode 248 ab2Rows = BinaryMatrix.decode 248 uRows :=
  BinaryMatrix.decode_mul 248 ababRows ab2Rows uRows u_check

set_option maxHeartbeats 4000000 in
private theorem u2_check : ∀ i : Fin 248,
    BinaryMatrix.rowProduct uRows[i.val]! uRows 248 = u2Rows[i.val]! := by
  decide +kernel

 theorem u2_product : BinaryMatrix.decode 248 uRows *
    BinaryMatrix.decode 248 uRows = BinaryMatrix.decode 248 u2Rows :=
  BinaryMatrix.decode_mul 248 uRows uRows u2Rows u2_check

set_option maxHeartbeats 4000000 in
private theorem u3_check : ∀ i : Fin 248,
    BinaryMatrix.rowProduct u2Rows[i.val]! uRows 248 = u3Rows[i.val]! := by
  decide +kernel

 theorem u3_product : BinaryMatrix.decode 248 u2Rows *
    BinaryMatrix.decode 248 uRows = BinaryMatrix.decode 248 u3Rows :=
  BinaryMatrix.decode_mul 248 u2Rows uRows u3Rows u3_check

set_option maxHeartbeats 4000000 in
private theorem rB_check : ∀ i : Fin 248,
    BinaryMatrix.rowProduct u3Rows[i.val]! u3Rows 248 = rBRows[i.val]! := by
  decide +kernel

 theorem rB_product : BinaryMatrix.decode 248 u3Rows *
    BinaryMatrix.decode 248 u3Rows = BinaryMatrix.decode 248 rBRows :=
  BinaryMatrix.decode_mul 248 u3Rows u3Rows rBRows rB_check

end Thompson.Simplicity.ThreeWordCertificate
