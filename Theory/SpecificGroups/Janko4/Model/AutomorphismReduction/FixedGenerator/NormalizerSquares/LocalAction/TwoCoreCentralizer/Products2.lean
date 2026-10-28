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

theorem product_xyxyy : packedMul xyxyRows w14Rows = xyxyyRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_tp2 : packedMul xyxyyRows xyxyyRows = tp2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_tp3 : packedMul xyxyyRows tp2Rows = tp3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_tp5 : packedMul tp2Rows tp3Rows = tp5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_tp6 : packedMul tp3Rows tp3Rows = tp6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_tp11 : packedMul tp5Rows tp6Rows = tp11Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t : packedMul tp11Rows tp11Rows = tRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_bb : packedMul bRows bRows = bbRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_bba : packedMul bbRows aRows = bbaRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_g : packedMul bbaRows bRows = gRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_gi : packedMul gRows giRows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedOne, get_ofFn]; decide +kernel)

theorem product_gia : packedMul giRows aRows = giaRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_ag : packedMul giaRows gRows = agRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_d : packedMul tRows agRows = dRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_d6p2 : packedMul dRows dRows = d6p2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_d6p3 : packedMul dRows d6p2Rows = d6p3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
