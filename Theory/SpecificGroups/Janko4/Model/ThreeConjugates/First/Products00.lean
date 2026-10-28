module

public import Theory.SpecificGroups.Janko4.Model.ThreeConjugates.First.Rows

/-!
# Packed certificate for the first J₄ generating triple

The explicit words specialize Revin--Zavarnitsine,
https://arxiv.org/abs/2505.05173v2, Theorem 1, to the first involution.
The ATLAS matrices `J4G1-f2r112B0` and words `J4G1-max2W1` are attributed in
`Model.Data` and `TwoCoreCentralizer.Words` (Wilson, Nickerson and Bray).
The witness was found by the untrusted search saved in the parent task's
`Scratch/JankoFourGeometry/Explore.py`. This file is reproduced by
`First/source/generate.py`; every product is checked by Lean's kernel.

With x=cx, y=cy, u=(xyxyy)^11, v=(ab)a(ab)⁻¹ and k=(vb²)^5(ab), set
 t=k(u(y⁻²uy²))k⁻¹, g=(vt)^5(ab), h=((bab⁻¹)(tb))^5 b.
The certificates show ga=tg and ha=(tb)h. Thus the three conjugates generate
a and t⁻¹(tb)=b. Only the literal generator closure is needed.
-/

@[expose] public section
namespace Janko4.ThreeConjugates.First
open Janko4.GeneratorCertificates

set_option maxRecDepth 10000

theorem product_firstXY : packedMul Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.cxRows Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.cyRows = firstXYRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_firstXYX : packedMul firstXYRows Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.cxRows = firstXYXRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_firstXYXY : packedMul firstXYXRows Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.cyRows = firstXYXYRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_firstXYXYY : packedMul firstXYXYRows Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.cyRows = firstXYXYYRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_firstUp2 : packedMul firstXYXYYRows firstXYXYYRows = firstUp2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_firstUp3 : packedMul firstXYXYYRows firstUp2Rows = firstUp3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_firstUp5 : packedMul firstUp2Rows firstUp3Rows = firstUp5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_firstUp6 : packedMul firstUp3Rows firstUp3Rows = firstUp6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.ThreeConjugates.First
