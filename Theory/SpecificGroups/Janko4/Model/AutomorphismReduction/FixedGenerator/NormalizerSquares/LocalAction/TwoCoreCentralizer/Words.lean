module

public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates

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

def w0 : Model := a * b

def w1 : Model := w0 * b

def w2 : Model := w0 * w1

def w3 : Model := w0 * w2

def w4 : Model := w2 ^ 5

def w5 : Model := w1 * b

def w6 : Model := w3 ^ 8

def w7 : Model := w0 ^ 9

def w8 : Model := w7⁻¹

def w9 : Model := w8 * w4

def w10 : Model := w9 * w7

def w11 : Model := w5 ^ 21

def w12 : Model := w11⁻¹

def w13 : Model := w12 * w6

def w14 : Model := w13 * w11

def xy : Model := w10 * w14

def xyx : Model := xy * w10

def xyxy : Model := xyx * w14

def xyxyy : Model := xyxy * w14

def t : Model := xyxyy ^ 22

def bb : Model := b * b

def bba : Model := bb * a

def g : Model := bba * b

def gi : Model := g⁻¹

def gia : Model := gi * a

def ag : Model := gia * g

def d : Model := t * ag

def d6 : Model := d ^ 6

def h : Model := d6 * gi

def hi : Model := h⁻¹

def hit : Model := hi * t

def ta : Model := hit * h

def hix : Model := hi * w10

def cx : Model := hix * h

def hiy : Model := hi * w14

def cy : Model := hiy * h

def cxa : Model := cx * a

def acx : Model := a * cx

def cya : Model := cy * a

def acy : Model := a * cy

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
