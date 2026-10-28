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

theorem product_w8 : packedMul w7Rows w8Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedOne, get_ofFn]; decide +kernel)

theorem product_w9 : packedMul w8Rows w4Rows = w9Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_w10 : packedMul w9Rows w7Rows = w10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_w11p2 : packedMul w5Rows w5Rows = w11p2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_w11p3 : packedMul w5Rows w11p2Rows = w11p3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_w11p5 : packedMul w11p2Rows w11p3Rows = w11p5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_w11p10 : packedMul w11p5Rows w11p5Rows = w11p10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_w11p6 : packedMul w11p3Rows w11p3Rows = w11p6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_w11p11 : packedMul w11p5Rows w11p6Rows = w11p11Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_w11 : packedMul w11p10Rows w11p11Rows = w11Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_w12 : packedMul w11Rows w12Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedOne, get_ofFn]; decide +kernel)

theorem product_w13 : packedMul w12Rows w6Rows = w13Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_w14 : packedMul w13Rows w11Rows = w14Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_xy : packedMul w10Rows w14Rows = xyRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_xyx : packedMul xyRows w10Rows = xyxRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_xyxy : packedMul xyxRows w14Rows = xyxyRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
