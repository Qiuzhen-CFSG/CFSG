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
private theorem w6_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct atlasBRows[i.val]! atlasARows.toList 0 = w6Rows[i.val]! := by
  decide +kernel

theorem w6_product : BinaryMatrix.decode 248 atlasBRows *
    BinaryMatrix.decode 248 atlasARows = BinaryMatrix.decode 248 w6Rows :=
  BinaryMatrix.decode_mul_list 248 atlasBRows atlasARows w6Rows (by decide) w6_check

set_option maxHeartbeats 4000000 in
private theorem w7_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct atlasARows[i.val]! w6Rows.toList 0 = w7Rows[i.val]! := by
  decide +kernel

theorem w7_product : BinaryMatrix.decode 248 atlasARows *
    BinaryMatrix.decode 248 w6Rows = BinaryMatrix.decode 248 w7Rows :=
  BinaryMatrix.decode_mul_list 248 atlasARows w6Rows w7Rows (by decide) w7_check

set_option maxHeartbeats 4000000 in
private theorem w8_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct w6Rows[i.val]! w6Rows.toList 0 = w8Rows[i.val]! := by
  decide +kernel

theorem w8_product : BinaryMatrix.decode 248 w6Rows *
    BinaryMatrix.decode 248 w6Rows = BinaryMatrix.decode 248 w8Rows :=
  BinaryMatrix.decode_mul_list 248 w6Rows w6Rows w8Rows (by decide) w8_check

set_option maxHeartbeats 4000000 in
private theorem w9_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct w7Rows[i.val]! w8Rows.toList 0 = w9Rows[i.val]! := by
  decide +kernel

theorem w9_product : BinaryMatrix.decode 248 w7Rows *
    BinaryMatrix.decode 248 w8Rows = BinaryMatrix.decode 248 w9Rows :=
  BinaryMatrix.decode_mul_list 248 w7Rows w8Rows w9Rows (by decide) w9_check

end Thompson.Simplicity.PrimeWordCertificate
