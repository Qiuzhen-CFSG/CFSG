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
private theorem w14_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct atlasARows[i.val]! w10Rows.toList 0 = w14Rows[i.val]! := by
  decide +kernel

theorem w14_product : BinaryMatrix.decode 248 atlasARows *
    BinaryMatrix.decode 248 w10Rows = BinaryMatrix.decode 248 w14Rows :=
  BinaryMatrix.decode_mul_list 248 atlasARows w10Rows w14Rows (by decide) w14_check

set_option maxHeartbeats 4000000 in
private theorem w15_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct w2Rows[i.val]! w6Rows.toList 0 = w15Rows[i.val]! := by
  decide +kernel

theorem w15_product : BinaryMatrix.decode 248 w2Rows *
    BinaryMatrix.decode 248 w6Rows = BinaryMatrix.decode 248 w15Rows :=
  BinaryMatrix.decode_mul_list 248 w2Rows w6Rows w15Rows (by decide) w15_check

set_option maxHeartbeats 4000000 in
private theorem w16_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct w14Rows[i.val]! w15Rows.toList 0 = w16Rows[i.val]! := by
  decide +kernel

theorem w16_product : BinaryMatrix.decode 248 w14Rows *
    BinaryMatrix.decode 248 w15Rows = BinaryMatrix.decode 248 w16Rows :=
  BinaryMatrix.decode_mul_list 248 w14Rows w15Rows w16Rows (by decide) w16_check

set_option maxHeartbeats 4000000 in
private theorem w17_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct w10Rows[i.val]! w2Rows.toList 0 = w17Rows[i.val]! := by
  decide +kernel

theorem w17_product : BinaryMatrix.decode 248 w10Rows *
    BinaryMatrix.decode 248 w2Rows = BinaryMatrix.decode 248 w17Rows :=
  BinaryMatrix.decode_mul_list 248 w10Rows w2Rows w17Rows (by decide) w17_check

end Thompson.Simplicity.PrimeWordCertificate
