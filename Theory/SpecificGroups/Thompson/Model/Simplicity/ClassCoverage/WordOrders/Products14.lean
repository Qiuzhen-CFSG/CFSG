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
private theorem r8p15_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct r8p7Rows[i.val]! r8p8Rows.toList 0 = r8p15Rows[i.val]! := by
  decide +kernel

theorem r8p15_product : BinaryMatrix.decode 248 r8p7Rows *
    BinaryMatrix.decode 248 r8p8Rows = BinaryMatrix.decode 248 r8p15Rows :=
  BinaryMatrix.decode_mul_list 248 r8p7Rows r8p8Rows r8p15Rows (by decide) r8p15_check

set_option maxHeartbeats 4000000 in
private theorem r8p16_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct r8p8Rows[i.val]! r8p8Rows.toList 0 = r8p16Rows[i.val]! := by
  decide +kernel

theorem r8p16_product : BinaryMatrix.decode 248 r8p8Rows *
    BinaryMatrix.decode 248 r8p8Rows = BinaryMatrix.decode 248 r8p16Rows :=
  BinaryMatrix.decode_mul_list 248 r8p8Rows r8p8Rows r8p16Rows (by decide) r8p16_check

set_option maxHeartbeats 4000000 in
private theorem r8p31_check : ∀ i : Fin 248,
    BinaryMatrix.listProduct r8p15Rows[i.val]! r8p16Rows.toList 0 = 2 ^ i.val := by
  decide +kernel

theorem r8p31_product : BinaryMatrix.decode 248 r8p15Rows *
    BinaryMatrix.decode 248 r8p16Rows = 1 :=
  BinaryMatrix.decode_mul_one_list 248 r8p15Rows r8p16Rows (by decide) r8p31_check

end Thompson.Simplicity.PrimeWordCertificate
