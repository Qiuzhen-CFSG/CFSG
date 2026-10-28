module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Words

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

def firstX : Model := Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.cx

def firstY : Model := Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.cy

def firstAB : Model := a * b

def firstB2 : Model := b * b

def firstXY : Model := firstX * firstY

def firstXYX : Model := firstXY * firstX

def firstXYXY : Model := firstXYX * firstY

def firstXYXYY : Model := firstXYXY * firstY

def firstU : Model := firstXYXYY ^ 11

def firstABi : Model := firstAB⁻¹

def firstABA : Model := firstAB * a

def firstV : Model := firstABA * firstABi

def firstVB2 : Model := firstV * firstB2

def firstK5 : Model := firstVB2 ^ 5

def firstK : Model := firstK5 * firstAB

def firstY2 : Model := firstY * firstY

def firstY2i : Model := firstY2⁻¹

def firstY2iU : Model := firstY2i * firstU

def firstUc : Model := firstY2iU * firstY2

def firstUUc : Model := firstU * firstUc

def firstKi : Model := firstK⁻¹

def firstKUUc : Model := firstK * firstUUc

def firstT : Model := firstKUUc * firstKi

def firstTB : Model := firstT * b

def firstVT : Model := firstV * firstT

def firstVT5 : Model := firstVT ^ 5

def firstG : Model := firstVT5 * firstAB

def firstBi : Model := b⁻¹

def firstBA : Model := b * a

def firstW : Model := firstBA * firstBi

def firstWTB : Model := firstW * firstTB

def firstWTB5 : Model := firstWTB ^ 5

def firstH : Model := firstWTB5 * b

def firstGA : Model := firstG * a

def firstHA : Model := firstH * a

end Janko4.ThreeConjugates.First
