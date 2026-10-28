module

public import Theory.SpecificGroups.Janko4.Model.ThreeConjugates.First.Words
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Evaluations
public import Theory.SpecificGroups.Janko4.Model.ThreeConjugates.First.Products00
public import Theory.SpecificGroups.Janko4.Model.ThreeConjugates.First.Products01
public import Theory.SpecificGroups.Janko4.Model.ThreeConjugates.First.Products02
public import Theory.SpecificGroups.Janko4.Model.ThreeConjugates.First.Products03
public import Theory.SpecificGroups.Janko4.Model.ThreeConjugates.First.Products04
public import Theory.SpecificGroups.Janko4.Model.ThreeConjugates.First.Products05

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

private theorem mul_certificate {g h : Model} {rs ss ts : Vector ℕ 112}
    (hg : toMatrix g = decodeRows rs) (hh : toMatrix h = decodeRows ss)
    (hc : packedMul rs ss = ts) : toMatrix (g * h) = decodeRows ts := by
  rw [map_mul, hg, hh, ← decode_packedMul, hc]

private theorem pow_certificate {g : Model} {m n : ℕ} {rs ss ts : Vector ℕ 112}
    (hg : toMatrix (g ^ m) = decodeRows rs) (hh : toMatrix (g ^ n) = decodeRows ss)
    (hc : packedMul rs ss = ts) : toMatrix (g ^ (m + n)) = decodeRows ts := by
  rw [pow_add]
  exact mul_certificate hg hh hc

private theorem inv_certificate {g : Model} {rs ss : Vector ℕ 112}
    (hg : toMatrix g = decodeRows rs) (hc : packedMul rs ss = packedOne) :
    toMatrix g⁻¹ = decodeRows ss := by
  have h : toMatrix g * decodeRows ss = 1 := by
    rw [hg, ← decode_packedMul, hc, decode_packedOne]
  calc
    toMatrix g⁻¹ = toMatrix g⁻¹ * 1 := (mul_one _).symm
    _ = toMatrix g⁻¹ * (toMatrix g * decodeRows ss) := by rw [h]
    _ = decodeRows ss := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

private theorem eval_a : toMatrix a = decodeRows aRows := rfl
private theorem eval_b : toMatrix b = decodeRows bRows := rfl

private theorem eval_firstX : toMatrix firstX = decodeRows (Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.cxRows) :=
  Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.eval_cx

private theorem eval_firstY : toMatrix firstY = decodeRows (Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.cyRows) :=
  Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.eval_cy

private theorem eval_firstAB : toMatrix firstAB = decodeRows (Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.w0Rows) :=
  Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.eval_w0

private theorem eval_firstB2 : toMatrix firstB2 = decodeRows (Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.bbRows) :=
  Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.eval_bb

theorem eval_firstXY : toMatrix firstXY = decodeRows firstXYRows :=
  mul_certificate eval_firstX eval_firstY product_firstXY

theorem eval_firstXYX : toMatrix firstXYX = decodeRows firstXYXRows :=
  mul_certificate eval_firstXY eval_firstX product_firstXYX

theorem eval_firstXYXY : toMatrix firstXYXY = decodeRows firstXYXYRows :=
  mul_certificate eval_firstXYX eval_firstY product_firstXYXY

theorem eval_firstXYXYY : toMatrix firstXYXYY = decodeRows firstXYXYYRows :=
  mul_certificate eval_firstXYXY eval_firstY product_firstXYXYY

private theorem base_firstU : toMatrix (firstXYXYY ^ 1) = decodeRows firstXYXYYRows := by
  simpa only [pow_one] using eval_firstXYXYY

theorem eval_firstUp2 : toMatrix (firstXYXYY ^ 2) = decodeRows firstUp2Rows :=
  pow_certificate (g := firstXYXYY) (m := 1) (n := 1) base_firstU base_firstU product_firstUp2

theorem eval_firstUp3 : toMatrix (firstXYXYY ^ 3) = decodeRows firstUp3Rows :=
  pow_certificate (g := firstXYXYY) (m := 1) (n := 2) base_firstU eval_firstUp2 product_firstUp3

theorem eval_firstUp5 : toMatrix (firstXYXYY ^ 5) = decodeRows firstUp5Rows :=
  pow_certificate (g := firstXYXYY) (m := 2) (n := 3) eval_firstUp2 eval_firstUp3 product_firstUp5

theorem eval_firstUp6 : toMatrix (firstXYXYY ^ 6) = decodeRows firstUp6Rows :=
  pow_certificate (g := firstXYXYY) (m := 3) (n := 3) eval_firstUp3 eval_firstUp3 product_firstUp6

theorem eval_firstU : toMatrix firstU = decodeRows firstURows :=
  pow_certificate (g := firstXYXYY) (m := 5) (n := 6) eval_firstUp5 eval_firstUp6 product_firstU

theorem eval_firstABi : toMatrix firstABi = decodeRows firstABiRows :=
  inv_certificate eval_firstAB product_firstABi

theorem eval_firstABA : toMatrix firstABA = decodeRows firstABARows :=
  mul_certificate eval_firstAB eval_a product_firstABA

theorem eval_firstV : toMatrix firstV = decodeRows firstVRows :=
  mul_certificate eval_firstABA eval_firstABi product_firstV

theorem eval_firstVB2 : toMatrix firstVB2 = decodeRows firstVB2Rows :=
  mul_certificate eval_firstV eval_firstB2 product_firstVB2

private theorem base_firstK5 : toMatrix (firstVB2 ^ 1) = decodeRows firstVB2Rows := by
  simpa only [pow_one] using eval_firstVB2

theorem eval_firstK5p2 : toMatrix (firstVB2 ^ 2) = decodeRows firstK5p2Rows :=
  pow_certificate (g := firstVB2) (m := 1) (n := 1) base_firstK5 base_firstK5 product_firstK5p2

theorem eval_firstK5p3 : toMatrix (firstVB2 ^ 3) = decodeRows firstK5p3Rows :=
  pow_certificate (g := firstVB2) (m := 1) (n := 2) base_firstK5 eval_firstK5p2 product_firstK5p3

theorem eval_firstK5 : toMatrix firstK5 = decodeRows firstK5Rows :=
  pow_certificate (g := firstVB2) (m := 2) (n := 3) eval_firstK5p2 eval_firstK5p3 product_firstK5

theorem eval_firstK : toMatrix firstK = decodeRows firstKRows :=
  mul_certificate eval_firstK5 eval_firstAB product_firstK

theorem eval_firstY2 : toMatrix firstY2 = decodeRows firstY2Rows :=
  mul_certificate eval_firstY eval_firstY product_firstY2

theorem eval_firstY2i : toMatrix firstY2i = decodeRows firstY2iRows :=
  inv_certificate eval_firstY2 product_firstY2i

theorem eval_firstY2iU : toMatrix firstY2iU = decodeRows firstY2iURows :=
  mul_certificate eval_firstY2i eval_firstU product_firstY2iU

theorem eval_firstUc : toMatrix firstUc = decodeRows firstUcRows :=
  mul_certificate eval_firstY2iU eval_firstY2 product_firstUc

theorem eval_firstUUc : toMatrix firstUUc = decodeRows firstUUcRows :=
  mul_certificate eval_firstU eval_firstUc product_firstUUc

theorem eval_firstKi : toMatrix firstKi = decodeRows firstKiRows :=
  inv_certificate eval_firstK product_firstKi

theorem eval_firstKUUc : toMatrix firstKUUc = decodeRows firstKUUcRows :=
  mul_certificate eval_firstK eval_firstUUc product_firstKUUc

theorem eval_firstT : toMatrix firstT = decodeRows firstTRows :=
  mul_certificate eval_firstKUUc eval_firstKi product_firstT

theorem eval_firstTB : toMatrix firstTB = decodeRows firstTBRows :=
  mul_certificate eval_firstT eval_b product_firstTB

theorem eval_firstVT : toMatrix firstVT = decodeRows firstVTRows :=
  mul_certificate eval_firstV eval_firstT product_firstVT

private theorem base_firstVT5 : toMatrix (firstVT ^ 1) = decodeRows firstVTRows := by
  simpa only [pow_one] using eval_firstVT

theorem eval_firstVT5p2 : toMatrix (firstVT ^ 2) = decodeRows firstVT5p2Rows :=
  pow_certificate (g := firstVT) (m := 1) (n := 1) base_firstVT5 base_firstVT5 product_firstVT5p2

theorem eval_firstVT5p3 : toMatrix (firstVT ^ 3) = decodeRows firstVT5p3Rows :=
  pow_certificate (g := firstVT) (m := 1) (n := 2) base_firstVT5 eval_firstVT5p2 product_firstVT5p3

theorem eval_firstVT5 : toMatrix firstVT5 = decodeRows firstVT5Rows :=
  pow_certificate (g := firstVT) (m := 2) (n := 3) eval_firstVT5p2 eval_firstVT5p3 product_firstVT5

theorem eval_firstG : toMatrix firstG = decodeRows firstGRows :=
  mul_certificate eval_firstVT5 eval_firstAB product_firstG

theorem eval_firstBi : toMatrix firstBi = decodeRows firstBiRows :=
  inv_certificate eval_b product_firstBi

theorem eval_firstBA : toMatrix firstBA = decodeRows firstBARows :=
  mul_certificate eval_b eval_a product_firstBA

theorem eval_firstW : toMatrix firstW = decodeRows firstWRows :=
  mul_certificate eval_firstBA eval_firstBi product_firstW

theorem eval_firstWTB : toMatrix firstWTB = decodeRows firstWTBRows :=
  mul_certificate eval_firstW eval_firstTB product_firstWTB

private theorem base_firstWTB5 : toMatrix (firstWTB ^ 1) = decodeRows firstWTBRows := by
  simpa only [pow_one] using eval_firstWTB

theorem eval_firstWTB5p2 : toMatrix (firstWTB ^ 2) = decodeRows firstWTB5p2Rows :=
  pow_certificate (g := firstWTB) (m := 1) (n := 1) base_firstWTB5 base_firstWTB5 product_firstWTB5p2

theorem eval_firstWTB5p3 : toMatrix (firstWTB ^ 3) = decodeRows firstWTB5p3Rows :=
  pow_certificate (g := firstWTB) (m := 1) (n := 2) base_firstWTB5 eval_firstWTB5p2 product_firstWTB5p3

theorem eval_firstWTB5 : toMatrix firstWTB5 = decodeRows firstWTB5Rows :=
  pow_certificate (g := firstWTB) (m := 2) (n := 3) eval_firstWTB5p2 eval_firstWTB5p3 product_firstWTB5

theorem eval_firstH : toMatrix firstH = decodeRows firstHRows :=
  mul_certificate eval_firstWTB5 eval_b product_firstH

theorem eval_firstGA : toMatrix firstGA = decodeRows firstGARows :=
  mul_certificate eval_firstG eval_a product_firstGA

theorem eval_firstHA : toMatrix firstHA = decodeRows firstHARows :=
  mul_certificate eval_firstH eval_a product_firstHA

/-- Multiplication certificate for the first conjugator. -/
theorem firstG_mul_a : firstG * a = firstT * firstG := by
  apply toMatrix_injective
  exact eval_firstGA.trans
    (mul_certificate eval_firstT eval_firstG product_firstTG).symm

/-- Multiplication certificate for the second conjugator. -/
theorem firstH_mul_a : firstH * a = firstTB * firstH := by
  apply toMatrix_injective
  exact eval_firstHA.trans
    (mul_certificate eval_firstTB eval_firstH product_firstTBH).symm

end Janko4.ThreeConjugates.First
