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
private theorem r4p5_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct r4p2Rows[i.val]! r4p3Rows.toList 0 = 2 ^ i.val := by
  decide +kernel

theorem r4p5_product : BinaryMatrix.decode 248 r4p2Rows *
    BinaryMatrix.decode 248 r4p3Rows = 1 :=
  BinaryMatrix.decode_mul_one_list 248 r4p2Rows r4p3Rows (by decide) r4p5_check

set_option maxHeartbeats 4000000 in
private theorem r5p2_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct w20Rows[i.val]! w20Rows.toList 0 = r5p2Rows[i.val]! := by
  decide +kernel

theorem r5p2_product : BinaryMatrix.decode 248 w20Rows *
    BinaryMatrix.decode 248 w20Rows = BinaryMatrix.decode 248 r5p2Rows :=
  BinaryMatrix.decode_mul_list 248 w20Rows w20Rows r5p2Rows (by decide) r5p2_check

set_option maxHeartbeats 4000000 in
private theorem r5p3_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct w20Rows[i.val]! r5p2Rows.toList 0 = r5p3Rows[i.val]! := by
  decide +kernel

theorem r5p3_product : BinaryMatrix.decode 248 w20Rows *
    BinaryMatrix.decode 248 r5p2Rows = BinaryMatrix.decode 248 r5p3Rows :=
  BinaryMatrix.decode_mul_list 248 w20Rows r5p2Rows r5p3Rows (by decide) r5p3_check

set_option maxHeartbeats 4000000 in
private theorem r5p4_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct r5p2Rows[i.val]! r5p2Rows.toList 0 = r5p4Rows[i.val]! := by
  decide +kernel

theorem r5p4_product : BinaryMatrix.decode 248 r5p2Rows *
    BinaryMatrix.decode 248 r5p2Rows = BinaryMatrix.decode 248 r5p4Rows :=
  BinaryMatrix.decode_mul_list 248 r5p2Rows r5p2Rows r5p4Rows (by decide) r5p4_check

end Thompson.Simplicity.PrimeWordCertificate
