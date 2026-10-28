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
private theorem w26_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct w24Rows[i.val]! w25Rows.toList 0 = w26Rows[i.val]! := by
  decide +kernel

theorem w26_product : BinaryMatrix.decode 248 w24Rows *
    BinaryMatrix.decode 248 w25Rows = BinaryMatrix.decode 248 w26Rows :=
  BinaryMatrix.decode_mul_list 248 w24Rows w25Rows w26Rows (by decide) w26_check

set_option maxHeartbeats 4000000 in
private theorem w27_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct w22Rows[i.val]! w26Rows.toList 0 = w27Rows[i.val]! := by
  decide +kernel

theorem w27_product : BinaryMatrix.decode 248 w22Rows *
    BinaryMatrix.decode 248 w26Rows = BinaryMatrix.decode 248 w27Rows :=
  BinaryMatrix.decode_mul_list 248 w22Rows w26Rows w27Rows (by decide) w27_check

set_option maxHeartbeats 4000000 in
private theorem w28_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct w2Rows[i.val]! w7Rows.toList 0 = w28Rows[i.val]! := by
  decide +kernel

theorem w28_product : BinaryMatrix.decode 248 w2Rows *
    BinaryMatrix.decode 248 w7Rows = BinaryMatrix.decode 248 w28Rows :=
  BinaryMatrix.decode_mul_list 248 w2Rows w7Rows w28Rows (by decide) w28_check

set_option maxHeartbeats 4000000 in
private theorem w29_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct w3Rows[i.val]! w7Rows.toList 0 = w29Rows[i.val]! := by
  decide +kernel

theorem w29_product : BinaryMatrix.decode 248 w3Rows *
    BinaryMatrix.decode 248 w7Rows = BinaryMatrix.decode 248 w29Rows :=
  BinaryMatrix.decode_mul_list 248 w3Rows w7Rows w29Rows (by decide) w29_check

end Thompson.Simplicity.PrimeWordCertificate
