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
private theorem w38_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct w35Rows[i.val]! w37Rows.toList 0 = w38Rows[i.val]! := by
  decide +kernel

theorem w38_product : BinaryMatrix.decode 248 w35Rows *
    BinaryMatrix.decode 248 w37Rows = BinaryMatrix.decode 248 w38Rows :=
  BinaryMatrix.decode_mul_list 248 w35Rows w37Rows w38Rows (by decide) w38_check

set_option maxHeartbeats 4000000 in
private theorem w39_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct w33Rows[i.val]! w38Rows.toList 0 = w39Rows[i.val]! := by
  decide +kernel

theorem w39_product : BinaryMatrix.decode 248 w33Rows *
    BinaryMatrix.decode 248 w38Rows = BinaryMatrix.decode 248 w39Rows :=
  BinaryMatrix.decode_mul_list 248 w33Rows w38Rows w39Rows (by decide) w39_check

set_option maxHeartbeats 4000000 in
private theorem r4p2_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct w5Rows[i.val]! w5Rows.toList 0 = r4p2Rows[i.val]! := by
  decide +kernel

theorem r4p2_product : BinaryMatrix.decode 248 w5Rows *
    BinaryMatrix.decode 248 w5Rows = BinaryMatrix.decode 248 r4p2Rows :=
  BinaryMatrix.decode_mul_list 248 w5Rows w5Rows r4p2Rows (by decide) r4p2_check

set_option maxHeartbeats 4000000 in
private theorem r4p3_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct w5Rows[i.val]! r4p2Rows.toList 0 = r4p3Rows[i.val]! := by
  decide +kernel

theorem r4p3_product : BinaryMatrix.decode 248 w5Rows *
    BinaryMatrix.decode 248 r4p2Rows = BinaryMatrix.decode 248 r4p3Rows :=
  BinaryMatrix.decode_mul_list 248 w5Rows r4p2Rows r4p3Rows (by decide) r4p3_check

end Thompson.Simplicity.PrimeWordCertificate
