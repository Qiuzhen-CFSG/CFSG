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
private theorem w10_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct atlasBRows[i.val]! atlasBRows.toList 0 = w10Rows[i.val]! := by
  decide +kernel

theorem w10_product : BinaryMatrix.decode 248 atlasBRows *
    BinaryMatrix.decode 248 atlasBRows = BinaryMatrix.decode 248 w10Rows :=
  BinaryMatrix.decode_mul_list 248 atlasBRows atlasBRows w10Rows (by decide) w10_check

set_option maxHeartbeats 4000000 in
private theorem w11_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct w6Rows[i.val]! w10Rows.toList 0 = w11Rows[i.val]! := by
  decide +kernel

theorem w11_product : BinaryMatrix.decode 248 w6Rows *
    BinaryMatrix.decode 248 w10Rows = BinaryMatrix.decode 248 w11Rows :=
  BinaryMatrix.decode_mul_list 248 w6Rows w10Rows w11Rows (by decide) w11_check

set_option maxHeartbeats 4000000 in
private theorem w12_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct w8Rows[i.val]! w11Rows.toList 0 = w12Rows[i.val]! := by
  decide +kernel

theorem w12_product : BinaryMatrix.decode 248 w8Rows *
    BinaryMatrix.decode 248 w11Rows = BinaryMatrix.decode 248 w12Rows :=
  BinaryMatrix.decode_mul_list 248 w8Rows w11Rows w12Rows (by decide) w12_check

set_option maxHeartbeats 4000000 in
private theorem w13_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct w9Rows[i.val]! w12Rows.toList 0 = w13Rows[i.val]! := by
  decide +kernel

theorem w13_product : BinaryMatrix.decode 248 w9Rows *
    BinaryMatrix.decode 248 w12Rows = BinaryMatrix.decode 248 w13Rows :=
  BinaryMatrix.decode_mul_list 248 w9Rows w12Rows w13Rows (by decide) w13_check

end Thompson.Simplicity.PrimeWordCertificate
