module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Elementary

/-!
# Native normalizer certificate data

The ATLAS J4G1-max3W1 words are aligned to the native octad-pullback F by
k=(r*r2*e51)^19*h*e1. Here h is the reversed GAP octad-transport word;
the ATLAS words themselves use ordinary multiplication. Literal products
below are discovery data, certified in the following bounded leaves.
Source: https://brauer.maths.qmul.ac.uk/Atlas/spor/J4/words/J4G1-max3W1 .
-/
@[expose] public noncomputable section
namespace Janko4.LocalStructure.LinearFive.NativeNormalizer
open Cardinality KernelCount
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel localX localY
def ab : Model := sourceA matrixA_mul_self * sourceB matrixB_pow_four
def b2 : Model := sourceB matrixB_pow_four * sourceB matrixB_pow_four
def b3 : Model := b2 * sourceB matrixB_pow_four
def ab3 : Model := sourceA matrixA_mul_self * b3
def t2 : Model := ab3 * ab3
def t4 : Model := t2 * t2
def it4 : Model := t4⁻¹
def ua : Model := it4 * sourceA matrixA_mul_self
def u : Model := ua * t4
def s2 : Model := ab * ab
def s4 : Model := s2 * s2
def s8 : Model := s4 * s4
def is8 : Model := s8⁻¹
def vb : Model := is8 * sourceB matrixB_pow_four
def v : Model := vb * s8
def v2 : Model := v * v
def v3 : Model := v2 * v
def w0 : Model := v2 * u
def w1 : Model := w0 * v3
def w2 : Model := w1 * u
def w3 : Model := w2 * v
def w : Model := w3 * u
def w4a : Model := w * w
def r : Model := w4a * w4a
def iu : Model := u⁻¹
def iv : Model := v⁻¹
def r1a : Model := iu * r
def r1 : Model := r1a * u
def r2a : Model := iv * r1
def r2 : Model := r2a * v
def z : Model := r * r2
def zt : Model := z * (generators 0 : Model)
def zt2 : Model := zt * zt
def zt4 : Model := zt2 * zt2
def zt8 : Model := zt4 * zt4
def zt16 : Model := zt8 * zt8
def zt18 : Model := zt16 * zt2
def g : Model := zt18 * zt
def hshared0 : Model := NativeWords.d5 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model) * (localY matrixA_mul_self matrixB_pow_four : Model)
def h0 : Model := NativeWords.d20 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model) * NativeWords.d30 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model)
def h1 : Model := h0 * NativeWords.d21 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model)
def h2 : Model := h1 * NativeWords.d15 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model)
def h3 : Model := h2 * hshared0
def h4 : Model := h3 * NativeWords.d8 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model)
def h5 : Model := h4 * hshared0
def h6 : Model := h5 * NativeWords.d41 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model)
def h7 : Model := h6 * NativeWords.d20 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model)
def h8 : Model := h7 * NativeWords.d19 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model)
def h9 : Model := h8 * NativeWords.d27 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model)
def h10 : Model := h9 * NativeWords.d15 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model)
def h11 : Model := h10 * NativeWords.d17 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model)
def h12 : Model := h11 * NativeWords.d40 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model)
def h13 : Model := h12 * NativeWords.d17 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model)
def h14 : Model := h13 * NativeWords.d16 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model)
def h15 : Model := h14 * hshared0
def h16 : Model := h15 * NativeWords.d12 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model)
def h17 : Model := h16 * NativeWords.d19 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model)
def h18 : Model := h17 * NativeWords.d14 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model)
def h19 : Model := h18 * NativeWords.d43 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model)
def h20 : Model := h19 * NativeWords.d9 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model)
def gh : Model := g * h20
def k : Model := gh * (kernelValue 1 : Model)
def ik : Model := k⁻¹
def n0a : Model := ik * u
def n0 : Model := n0a * k
def n1a : Model := ik * v
def n1 : Model := n1a * k
def m3 : Model := (generators 0 : Model) * (generators 1 : Model)
def m7 : Model := m3 * (generators 2 : Model)
def m23 : Model := m7 * (generators 4 : Model)
def m55 : Model := m23 * (generators 5 : Model)
def m119 : Model := m55 * (generators 6 : Model)
def m247 : Model := m119 * (generators 7 : Model)
def m36 : Model := (generators 2 : Model) * (generators 5 : Model)
def m100 : Model := m36 * (generators 6 : Model)
def m356 : Model := m100 * (generators 8 : Model)
def m868 : Model := m356 * (generators 9 : Model)
def m24 : Model := (generators 3 : Model) * (generators 4 : Model)
def m35 : Model := m3 * (generators 5 : Model)
def m291 : Model := m35 * (generators 8 : Model)
def m803 : Model := m291 * (generators 9 : Model)
def m39 : Model := m7 * (generators 5 : Model)
def m295 : Model := m39 * (generators 8 : Model)
def m807 : Model := m295 * (generators 9 : Model)
def m11 : Model := m3 * (generators 3 : Model)
def m267 : Model := m11 * (generators 8 : Model)
def m779 : Model := m267 * (generators 9 : Model)
def m129 : Model := (generators 0 : Model) * (generators 7 : Model)
def m385 : Model := m129 * (generators 8 : Model)
def m897 : Model := m385 * (generators 9 : Model)
def m6 : Model := (generators 1 : Model) * (generators 2 : Model)
def m22 : Model := m6 * (generators 4 : Model)
def m54 : Model := m22 * (generators 5 : Model)
def m118 : Model := m54 * (generators 6 : Model)
def m246 : Model := m118 * (generators 7 : Model)
def m502 : Model := m246 * (generators 8 : Model)
def m38 : Model := m6 * (generators 5 : Model)
def m102 : Model := m38 * (generators 6 : Model)
def m358 : Model := m102 * (generators 8 : Model)
def m10 : Model := (generators 1 : Model) * (generators 3 : Model)
def m42 : Model := m10 * (generators 5 : Model)
def m106 : Model := m42 * (generators 6 : Model)
def m234 : Model := m106 * (generators 7 : Model)
def m746 : Model := m234 * (generators 9 : Model)
def m18 : Model := (generators 1 : Model) * (generators 4 : Model)
def m82 : Model := m18 * (generators 6 : Model)
def m210 : Model := m82 * (generators 7 : Model)
def m722 : Model := m210 * (generators 9 : Model)
def m12 : Model := (generators 2 : Model) * (generators 3 : Model)
def m19 : Model := m3 * (generators 4 : Model)
def m83 : Model := m19 * (generators 6 : Model)
def m140 : Model := m12 * (generators 7 : Model)
def m396 : Model := m140 * (generators 8 : Model)
def m44 : Model := m12 * (generators 5 : Model)
def m108 : Model := m44 * (generators 6 : Model)
def m236 : Model := m108 * (generators 7 : Model)
def m492 : Model := m236 * (generators 8 : Model)
def m88 : Model := m24 * (generators 6 : Model)
def m600 : Model := m88 * (generators 9 : Model)
def m20 : Model := (generators 2 : Model) * (generators 4 : Model)
def m52 : Model := m20 * (generators 5 : Model)
def m116 : Model := m52 * (generators 6 : Model)
def m27 : Model := m11 * (generators 4 : Model)
def m91 : Model := m27 * (generators 6 : Model)
def m603 : Model := m91 * (generators 9 : Model)
end Janko4.LocalStructure.LinearFive.NativeNormalizer
