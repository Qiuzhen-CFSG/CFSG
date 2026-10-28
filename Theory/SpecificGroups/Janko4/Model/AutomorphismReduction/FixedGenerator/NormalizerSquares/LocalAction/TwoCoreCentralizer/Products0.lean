module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Rows

/-!
# Explicit words bridging the ATLAS second local subgroup to the first generator

The original word program is `J4G1-max2W1` from the online ATLAS of Finite
Group Representations (R. A. Wilson, S. J. Nickerson, J. N. Bray):
https://brauer.maths.qmul.ac.uk/Atlas/spor/J4/words/J4G1-max2W1 .
Its outputs X,Y centralize t = (XYXYY)^22. With g = b*b*a*b,
d = t*g⁻¹*a*g and h = d^6*g⁻¹, the matrix identities certify h⁻¹*t*h = a
and that h⁻¹*X*h and h⁻¹*Y*h commute with a. All words are evaluated in
the literal matrix carrier. No assertion of full centralizer generation,
two-core structure, group order or simplicity is made here.

Row tables are untrusted witnesses. Packed multiplication is checked by
`decide +kernel`, then transferred by `decode_packedMul`. Source matrices
and bit conventions are documented in `Janko4.Model.Data`.
-/

@[expose] public section

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open Janko4.GeneratorCertificates

set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem product_w0 : packedMul aRows bRows = w0Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_w1 : packedMul w0Rows bRows = w1Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_w2 : packedMul w0Rows w1Rows = w2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_w3 : packedMul w0Rows w2Rows = w3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_w4p2 : packedMul w2Rows w2Rows = w4p2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_w4p3 : packedMul w2Rows w4p2Rows = w4p3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_w4 : packedMul w4p2Rows w4p3Rows = w4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_w5 : packedMul w1Rows bRows = w5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_w6p2 : packedMul w3Rows w3Rows = w6p2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_w6p4 : packedMul w6p2Rows w6p2Rows = w6p4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_w6 : packedMul w6p4Rows w6p4Rows = w6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_w7p2 : packedMul w0Rows w0Rows = w7p2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_w7p4 : packedMul w7p2Rows w7p2Rows = w7p4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_w7p3 : packedMul w0Rows w7p2Rows = w7p3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_w7p5 : packedMul w7p2Rows w7p3Rows = w7p5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_w7 : packedMul w7p4Rows w7p5Rows = w7Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
