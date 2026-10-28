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

theorem product_d6 : packedMul d6p3Rows d6p3Rows = d6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_h : packedMul d6Rows giRows = hRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_hi : packedMul hRows hiRows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedOne, get_ofFn]; decide +kernel)

theorem product_hit : packedMul hiRows tRows = hitRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_ta : packedMul hitRows hRows = taRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_hix : packedMul hiRows w10Rows = hixRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_cx : packedMul hixRows hRows = cxRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_hiy : packedMul hiRows w14Rows = hiyRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_cy : packedMul hiyRows hRows = cyRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_cxa : packedMul cxRows aRows = cxaRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_acx : packedMul aRows cxRows = acxRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_cya : packedMul cyRows aRows = cyaRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_acy : packedMul aRows cyRows = acyRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
