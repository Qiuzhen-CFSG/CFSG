module

public import Theory.SpecificGroups.Thompson.Model.Simplicity.NormalGenerationLow.ThreeB.Rows

/-!
# Matrix witnesses for normal generation by the second Thompson three-word

Writing `r = (ababab²)^6`, these products certify `(b*a*r*(a*b²)*a)^27 = 1`.
The original word products are reused from `ClassCoverage.Threes`; the new
packed products are checked in the kernel via `BinaryMatrix.decode_mul`.
Source matrices: ATLAS Th, https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/Th/ .
See `Model/source/README.md` and `ThreeB/source/README.md` for provenance.
-/

@[expose] public section
namespace Thompson.Simplicity.ThreeBNormalCertificate
open ThreeWordCertificate
set_option maxRecDepth 10000

set_option maxHeartbeats 4000000 in
private theorem t2_check : ∀ i : Fin 248,
    BinaryMatrix.rowProduct tRows[i.val]! tRows 248 = t2Rows[i.val]! := by
  decide +kernel

 theorem t2_product : BinaryMatrix.decode 248 tRows *
    BinaryMatrix.decode 248 tRows = BinaryMatrix.decode 248 t2Rows :=
  BinaryMatrix.decode_mul 248 tRows tRows t2Rows t2_check

set_option maxHeartbeats 4000000 in
private theorem t3_check : ∀ i : Fin 248,
    BinaryMatrix.rowProduct t2Rows[i.val]! tRows 248 = t3Rows[i.val]! := by
  decide +kernel

 theorem t3_product : BinaryMatrix.decode 248 t2Rows *
    BinaryMatrix.decode 248 tRows = BinaryMatrix.decode 248 t3Rows :=
  BinaryMatrix.decode_mul 248 t2Rows tRows t3Rows t3_check

set_option maxHeartbeats 4000000 in
private theorem t6_check : ∀ i : Fin 248,
    BinaryMatrix.rowProduct t3Rows[i.val]! t3Rows 248 = t6Rows[i.val]! := by
  decide +kernel

 theorem t6_product : BinaryMatrix.decode 248 t3Rows *
    BinaryMatrix.decode 248 t3Rows = BinaryMatrix.decode 248 t6Rows :=
  BinaryMatrix.decode_mul 248 t3Rows t3Rows t6Rows t6_check

set_option maxHeartbeats 4000000 in
private theorem t12_check : ∀ i : Fin 248,
    BinaryMatrix.rowProduct t6Rows[i.val]! t6Rows 248 = t12Rows[i.val]! := by
  decide +kernel

 theorem t12_product : BinaryMatrix.decode 248 t6Rows *
    BinaryMatrix.decode 248 t6Rows = BinaryMatrix.decode 248 t12Rows :=
  BinaryMatrix.decode_mul 248 t6Rows t6Rows t12Rows t12_check

end Thompson.Simplicity.ThreeBNormalCertificate
