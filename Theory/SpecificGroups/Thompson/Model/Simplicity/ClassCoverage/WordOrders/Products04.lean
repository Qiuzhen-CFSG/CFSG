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
private theorem w18_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct w17Rows[i.val]! w11Rows.toList 0 = w18Rows[i.val]! := by
  decide +kernel

theorem w18_product : BinaryMatrix.decode 248 w17Rows *
    BinaryMatrix.decode 248 w11Rows = BinaryMatrix.decode 248 w18Rows :=
  BinaryMatrix.decode_mul_list 248 w17Rows w11Rows w18Rows (by decide) w18_check

set_option maxHeartbeats 4000000 in
private theorem w19_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct w16Rows[i.val]! w18Rows.toList 0 = w19Rows[i.val]! := by
  decide +kernel

theorem w19_product : BinaryMatrix.decode 248 w16Rows *
    BinaryMatrix.decode 248 w18Rows = BinaryMatrix.decode 248 w19Rows :=
  BinaryMatrix.decode_mul_list 248 w16Rows w18Rows w19Rows (by decide) w19_check

set_option maxHeartbeats 4000000 in
private theorem w20_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct w13Rows[i.val]! w19Rows.toList 0 = w20Rows[i.val]! := by
  decide +kernel

theorem w20_product : BinaryMatrix.decode 248 w13Rows *
    BinaryMatrix.decode 248 w19Rows = BinaryMatrix.decode 248 w20Rows :=
  BinaryMatrix.decode_mul_list 248 w13Rows w19Rows w20Rows (by decide) w20_check

set_option maxHeartbeats 4000000 in
private theorem w21_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct w7Rows[i.val]! w3Rows.toList 0 = w21Rows[i.val]! := by
  decide +kernel

theorem w21_product : BinaryMatrix.decode 248 w7Rows *
    BinaryMatrix.decode 248 w3Rows = BinaryMatrix.decode 248 w21Rows :=
  BinaryMatrix.decode_mul_list 248 w7Rows w3Rows w21Rows (by decide) w21_check

end Thompson.Simplicity.PrimeWordCertificate
