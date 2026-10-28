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
private theorem w34_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct w6Rows[i.val]! w3Rows.toList 0 = w34Rows[i.val]! := by
  decide +kernel

theorem w34_product : BinaryMatrix.decode 248 w6Rows *
    BinaryMatrix.decode 248 w3Rows = BinaryMatrix.decode 248 w34Rows :=
  BinaryMatrix.decode_mul_list 248 w6Rows w3Rows w34Rows (by decide) w34_check

set_option maxHeartbeats 4000000 in
private theorem w35_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct w34Rows[i.val]! w29Rows.toList 0 = w35Rows[i.val]! := by
  decide +kernel

theorem w35_product : BinaryMatrix.decode 248 w34Rows *
    BinaryMatrix.decode 248 w29Rows = BinaryMatrix.decode 248 w35Rows :=
  BinaryMatrix.decode_mul_list 248 w34Rows w29Rows w35Rows (by decide) w35_check

set_option maxHeartbeats 4000000 in
private theorem w36_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct w3Rows[i.val]! w14Rows.toList 0 = w36Rows[i.val]! := by
  decide +kernel

theorem w36_product : BinaryMatrix.decode 248 w3Rows *
    BinaryMatrix.decode 248 w14Rows = BinaryMatrix.decode 248 w36Rows :=
  BinaryMatrix.decode_mul_list 248 w3Rows w14Rows w36Rows (by decide) w36_check

set_option maxHeartbeats 4000000 in
private theorem w37_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct w29Rows[i.val]! w36Rows.toList 0 = w37Rows[i.val]! := by
  decide +kernel

theorem w37_product : BinaryMatrix.decode 248 w29Rows *
    BinaryMatrix.decode 248 w36Rows = BinaryMatrix.decode 248 w37Rows :=
  BinaryMatrix.decode_mul_list 248 w29Rows w36Rows w37Rows (by decide) w37_check

end Thompson.Simplicity.PrimeWordCertificate
