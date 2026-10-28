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
private theorem w2_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct atlasARows[i.val]! atlasBRows.toList 0 = w2Rows[i.val]! := by
  decide +kernel

theorem w2_product : BinaryMatrix.decode 248 atlasARows *
    BinaryMatrix.decode 248 atlasBRows = BinaryMatrix.decode 248 w2Rows :=
  BinaryMatrix.decode_mul_list 248 atlasARows atlasBRows w2Rows (by decide) w2_check

set_option maxHeartbeats 4000000 in
private theorem w3_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct atlasBRows[i.val]! w2Rows.toList 0 = w3Rows[i.val]! := by
  decide +kernel

theorem w3_product : BinaryMatrix.decode 248 atlasBRows *
    BinaryMatrix.decode 248 w2Rows = BinaryMatrix.decode 248 w3Rows :=
  BinaryMatrix.decode_mul_list 248 atlasBRows w2Rows w3Rows (by decide) w3_check

set_option maxHeartbeats 4000000 in
private theorem w4_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct w2Rows[i.val]! w3Rows.toList 0 = w4Rows[i.val]! := by
  decide +kernel

theorem w4_product : BinaryMatrix.decode 248 w2Rows *
    BinaryMatrix.decode 248 w3Rows = BinaryMatrix.decode 248 w4Rows :=
  BinaryMatrix.decode_mul_list 248 w2Rows w3Rows w4Rows (by decide) w4_check

set_option maxHeartbeats 4000000 in
private theorem w5_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct w4Rows[i.val]! w4Rows.toList 0 = w5Rows[i.val]! := by
  decide +kernel

theorem w5_product : BinaryMatrix.decode 248 w4Rows *
    BinaryMatrix.decode 248 w4Rows = BinaryMatrix.decode 248 w5Rows :=
  BinaryMatrix.decode_mul_list 248 w4Rows w4Rows w5Rows (by decide) w5_check

end Thompson.Simplicity.PrimeWordCertificate
