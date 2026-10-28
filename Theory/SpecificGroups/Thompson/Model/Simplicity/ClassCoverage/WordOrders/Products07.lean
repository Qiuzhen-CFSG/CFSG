module

public import Theory.SpecificGroups.Thompson.Model.Simplicity.ClassCoverage.WordOrders.Rows
public import Theory.SpecificGroups.Thompson.Model.Simplicity.ClassCoverage.WordOrders.RowChecker

/-!
# Packed certificates for Thompson prime representative orders

Literal packed rows witness products in the fixed 248-dimensional binary
representation. `BinaryMatrix.decode_mul_list` turns kernel-checked row products
into matrix identities. The Python generator supplies no proof oracle.

Source: https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/Th/ , class words
(R. A. Wilson, S. J. Nickerson and J. N. Bray). Matrix provenance is in
`Model/source/README.md`; reproduction is in `WordOrders/source/Generate.py`.
-/

@[expose] public section
namespace Thompson.Simplicity.PrimeWordCertificate
set_option maxRecDepth 10000

set_option maxHeartbeats 4000000 in
private theorem w30_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct w28Rows[i.val]! w29Rows.toList 0 = w30Rows[i.val]! := by
  decide +kernel

theorem w30_product : BinaryMatrix.decode 248 w28Rows *
    BinaryMatrix.decode 248 w29Rows = BinaryMatrix.decode 248 w30Rows :=
  BinaryMatrix.decode_mul_list 248 w28Rows w29Rows w30Rows (by decide) w30_check

set_option maxHeartbeats 4000000 in
private theorem w31_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct w3Rows[i.val]! w3Rows.toList 0 = w31Rows[i.val]! := by
  decide +kernel

theorem w31_product : BinaryMatrix.decode 248 w3Rows *
    BinaryMatrix.decode 248 w3Rows = BinaryMatrix.decode 248 w31Rows :=
  BinaryMatrix.decode_mul_list 248 w3Rows w3Rows w31Rows (by decide) w31_check

set_option maxHeartbeats 4000000 in
private theorem w32_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct w31Rows[i.val]! w29Rows.toList 0 = w32Rows[i.val]! := by
  decide +kernel

theorem w32_product : BinaryMatrix.decode 248 w31Rows *
    BinaryMatrix.decode 248 w29Rows = BinaryMatrix.decode 248 w32Rows :=
  BinaryMatrix.decode_mul_list 248 w31Rows w29Rows w32Rows (by decide) w32_check

set_option maxHeartbeats 4000000 in
private theorem w33_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct w30Rows[i.val]! w32Rows.toList 0 = w33Rows[i.val]! := by
  decide +kernel

theorem w33_product : BinaryMatrix.decode 248 w30Rows *
    BinaryMatrix.decode 248 w32Rows = BinaryMatrix.decode 248 w33Rows :=
  BinaryMatrix.decode_mul_list 248 w30Rows w32Rows w33Rows (by decide) w33_check

end Thompson.Simplicity.PrimeWordCertificate
