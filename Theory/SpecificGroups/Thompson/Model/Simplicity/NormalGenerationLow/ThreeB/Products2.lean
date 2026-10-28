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
private theorem t24_check : ∀ i : Fin 248,
    BinaryMatrix.rowProduct t12Rows[i.val]! t12Rows 248 = t24Rows[i.val]! := by
  decide +kernel

 theorem t24_product : BinaryMatrix.decode 248 t12Rows *
    BinaryMatrix.decode 248 t12Rows = BinaryMatrix.decode 248 t24Rows :=
  BinaryMatrix.decode_mul 248 t12Rows t12Rows t24Rows t24_check

set_option maxHeartbeats 4000000 in
private theorem t27_check : ∀ i : Fin 248,
    BinaryMatrix.rowProduct t24Rows[i.val]! t3Rows 248 = 2 ^ i.val := by
  decide +kernel

 theorem t27_product : BinaryMatrix.decode 248 t24Rows *
    BinaryMatrix.decode 248 t3Rows = 1 :=
  BinaryMatrix.decode_mul_one 248 t24Rows t3Rows t27_check

end Thompson.Simplicity.ThreeBNormalCertificate
