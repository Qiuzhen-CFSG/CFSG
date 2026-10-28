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
private theorem r5p7_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct r5p3Rows[i.val]! r5p4Rows.toList 0 = 2 ^ i.val := by
  decide +kernel

theorem r5p7_product : BinaryMatrix.decode 248 r5p3Rows *
    BinaryMatrix.decode 248 r5p4Rows = 1 :=
  BinaryMatrix.decode_mul_one_list 248 r5p3Rows r5p4Rows (by decide) r5p7_check

set_option maxHeartbeats 4000000 in
private theorem r6p2_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct w27Rows[i.val]! w27Rows.toList 0 = r6p2Rows[i.val]! := by
  decide +kernel

theorem r6p2_product : BinaryMatrix.decode 248 w27Rows *
    BinaryMatrix.decode 248 w27Rows = BinaryMatrix.decode 248 r6p2Rows :=
  BinaryMatrix.decode_mul_list 248 w27Rows w27Rows r6p2Rows (by decide) r6p2_check

set_option maxHeartbeats 4000000 in
private theorem r6p3_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct w27Rows[i.val]! r6p2Rows.toList 0 = r6p3Rows[i.val]! := by
  decide +kernel

theorem r6p3_product : BinaryMatrix.decode 248 w27Rows *
    BinaryMatrix.decode 248 r6p2Rows = BinaryMatrix.decode 248 r6p3Rows :=
  BinaryMatrix.decode_mul_list 248 w27Rows r6p2Rows r6p3Rows (by decide) r6p3_check

set_option maxHeartbeats 4000000 in
private theorem r6p6_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct r6p3Rows[i.val]! r6p3Rows.toList 0 = r6p6Rows[i.val]! := by
  decide +kernel

theorem r6p6_product : BinaryMatrix.decode 248 r6p3Rows *
    BinaryMatrix.decode 248 r6p3Rows = BinaryMatrix.decode 248 r6p6Rows :=
  BinaryMatrix.decode_mul_list 248 r6p3Rows r6p3Rows r6p6Rows (by decide) r6p6_check

end Thompson.Simplicity.PrimeWordCertificate
