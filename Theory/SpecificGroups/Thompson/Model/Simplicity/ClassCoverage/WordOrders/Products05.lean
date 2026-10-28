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
private theorem w22_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct w21Rows[i.val]! w9Rows.toList 0 = w22Rows[i.val]! := by
  decide +kernel

theorem w22_product : BinaryMatrix.decode 248 w21Rows *
    BinaryMatrix.decode 248 w9Rows = BinaryMatrix.decode 248 w22Rows :=
  BinaryMatrix.decode_mul_list 248 w21Rows w9Rows w22Rows (by decide) w22_check

set_option maxHeartbeats 4000000 in
private theorem w23_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct w2Rows[i.val]! w2Rows.toList 0 = w23Rows[i.val]! := by
  decide +kernel

theorem w23_product : BinaryMatrix.decode 248 w2Rows *
    BinaryMatrix.decode 248 w2Rows = BinaryMatrix.decode 248 w23Rows :=
  BinaryMatrix.decode_mul_list 248 w2Rows w2Rows w23Rows (by decide) w23_check

set_option maxHeartbeats 4000000 in
private theorem w24_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct w3Rows[i.val]! w23Rows.toList 0 = w24Rows[i.val]! := by
  decide +kernel

theorem w24_product : BinaryMatrix.decode 248 w3Rows *
    BinaryMatrix.decode 248 w23Rows = BinaryMatrix.decode 248 w24Rows :=
  BinaryMatrix.decode_mul_list 248 w3Rows w23Rows w24Rows (by decide) w24_check

set_option maxHeartbeats 4000000 in
private theorem w25_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct w3Rows[i.val]! w11Rows.toList 0 = w25Rows[i.val]! := by
  decide +kernel

theorem w25_product : BinaryMatrix.decode 248 w3Rows *
    BinaryMatrix.decode 248 w11Rows = BinaryMatrix.decode 248 w25Rows :=
  BinaryMatrix.decode_mul_list 248 w3Rows w11Rows w25Rows (by decide) w25_check

end Thompson.Simplicity.PrimeWordCertificate
