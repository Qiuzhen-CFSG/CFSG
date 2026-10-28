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
private theorem r8p3_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct w39Rows[i.val]! r8p2Rows.toList 0 = r8p3Rows[i.val]! := by
  decide +kernel

theorem r8p3_product : BinaryMatrix.decode 248 w39Rows *
    BinaryMatrix.decode 248 r8p2Rows = BinaryMatrix.decode 248 r8p3Rows :=
  BinaryMatrix.decode_mul_list 248 w39Rows r8p2Rows r8p3Rows (by decide) r8p3_check

set_option maxHeartbeats 4000000 in
private theorem r8p4_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct r8p2Rows[i.val]! r8p2Rows.toList 0 = r8p4Rows[i.val]! := by
  decide +kernel

theorem r8p4_product : BinaryMatrix.decode 248 r8p2Rows *
    BinaryMatrix.decode 248 r8p2Rows = BinaryMatrix.decode 248 r8p4Rows :=
  BinaryMatrix.decode_mul_list 248 r8p2Rows r8p2Rows r8p4Rows (by decide) r8p4_check

set_option maxHeartbeats 4000000 in
private theorem r8p7_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct r8p3Rows[i.val]! r8p4Rows.toList 0 = r8p7Rows[i.val]! := by
  decide +kernel

theorem r8p7_product : BinaryMatrix.decode 248 r8p3Rows *
    BinaryMatrix.decode 248 r8p4Rows = BinaryMatrix.decode 248 r8p7Rows :=
  BinaryMatrix.decode_mul_list 248 r8p3Rows r8p4Rows r8p7Rows (by decide) r8p7_check

set_option maxHeartbeats 4000000 in
private theorem r8p8_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct r8p4Rows[i.val]! r8p4Rows.toList 0 = r8p8Rows[i.val]! := by
  decide +kernel

theorem r8p8_product : BinaryMatrix.decode 248 r8p4Rows *
    BinaryMatrix.decode 248 r8p4Rows = BinaryMatrix.decode 248 r8p8Rows :=
  BinaryMatrix.decode_mul_list 248 r8p4Rows r8p4Rows r8p8Rows (by decide) r8p8_check

end Thompson.Simplicity.PrimeWordCertificate
