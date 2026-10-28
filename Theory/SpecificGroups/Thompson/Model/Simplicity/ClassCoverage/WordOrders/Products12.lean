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
private theorem r6p4_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct r6p2Rows[i.val]! r6p2Rows.toList 0 = r6p4Rows[i.val]! := by
  decide +kernel

theorem r6p4_product : BinaryMatrix.decode 248 r6p2Rows *
    BinaryMatrix.decode 248 r6p2Rows = BinaryMatrix.decode 248 r6p4Rows :=
  BinaryMatrix.decode_mul_list 248 r6p2Rows r6p2Rows r6p4Rows (by decide) r6p4_check

set_option maxHeartbeats 4000000 in
private theorem r6p7_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct r6p3Rows[i.val]! r6p4Rows.toList 0 = r6p7Rows[i.val]! := by
  decide +kernel

theorem r6p7_product : BinaryMatrix.decode 248 r6p3Rows *
    BinaryMatrix.decode 248 r6p4Rows = BinaryMatrix.decode 248 r6p7Rows :=
  BinaryMatrix.decode_mul_list 248 r6p3Rows r6p4Rows r6p7Rows (by decide) r6p7_check

set_option maxHeartbeats 4000000 in
private theorem r6p13_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct r6p6Rows[i.val]! r6p7Rows.toList 0 = 2 ^ i.val := by
  decide +kernel

theorem r6p13_product : BinaryMatrix.decode 248 r6p6Rows *
    BinaryMatrix.decode 248 r6p7Rows = 1 :=
  BinaryMatrix.decode_mul_one_list 248 r6p6Rows r6p7Rows (by decide) r6p13_check

set_option maxHeartbeats 4000000 in
private theorem r8p2_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct w39Rows[i.val]! w39Rows.toList 0 = r8p2Rows[i.val]! := by
  decide +kernel

theorem r8p2_product : BinaryMatrix.decode 248 w39Rows *
    BinaryMatrix.decode 248 w39Rows = BinaryMatrix.decode 248 r8p2Rows :=
  BinaryMatrix.decode_mul_list 248 w39Rows w39Rows r8p2Rows (by decide) r8p2_check

end Thompson.Simplicity.PrimeWordCertificate
