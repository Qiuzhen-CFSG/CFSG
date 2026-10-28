module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Lifts
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.KernelOrbits.Coordinates

/-!
# Shared words for the native Figure 1/2 lifts

Concatenation shares repeated subwords without changing the literal markings.
The six final lists are checked against the original words in `Data`.
Source: Kleidman--Wilson (1988), Figures 1/2; ATLAS max1 generators.
-/

@[expose] public noncomputable section
namespace Janko4.LocalStructure.ElementaryEightGeometry
namespace LiftWords
def w0 : List (Fin 4) := [0]
def w1 : List (Fin 4) := [1]
def w2 : List (Fin 4) := [2]
def w3 : List (Fin 4) := [3]
def w4 : List (Fin 4) := w0 ++ w1
def w5 : List (Fin 4) := w0 ++ w3
def w6 : List (Fin 4) := w2 ++ w3
def w7 : List (Fin 4) := w2 ++ w1
def w8 : List (Fin 4) := w4 ++ w4
def w9 : List (Fin 4) := w5 ++ w5
def w10 : List (Fin 4) := w7 ++ w6
def w11 : List (Fin 4) := w6 ++ w6
def w12 : List (Fin 4) := w5 ++ w8
def w13 : List (Fin 4) := w7 ++ w7
def w14 : List (Fin 4) := w4 ++ w9
def w15 : List (Fin 4) := w10 ++ w10
def w16 : List (Fin 4) := w5 ++ w14
def w17 : List (Fin 4) := w4 ++ w12
def w18 : List (Fin 4) := w10 ++ w7
def w19 : List (Fin 4) := w17 ++ w8
def w20 : List (Fin 4) := w11 ++ w6
def w21 : List (Fin 4) := w14 ++ w12
def w22 : List (Fin 4) := w10 ++ w6
def w23 : List (Fin 4) := w13 ++ w13
def w24 : List (Fin 4) := w5 ++ w4
def w25 : List (Fin 4) := w11 ++ w11
def w26 : List (Fin 4) := w18 ++ w18
def w27 : List (Fin 4) := w19 ++ w15
def w28 : List (Fin 4) := w27 ++ w3
def w29 : List (Fin 4) := w28 ++ w21
def w30 : List (Fin 4) := w29 ++ w4
def w31 : List (Fin 4) := w6 ++ w7
def w32 : List (Fin 4) := w8 ++ w8
def w33 : List (Fin 4) := w10 ++ w20
def w34 : List (Fin 4) := w9 ++ w9
def w35 : List (Fin 4) := w10 ++ w11
def w36 : List (Fin 4) := w23 ++ w1
def w37 : List (Fin 4) := w7 ++ w1
def w38 : List (Fin 4) := w24 ++ w16
def w39 : List (Fin 4) := w21 ++ w30
def w40 : List (Fin 4) := w22 ++ w15
def w41 : List (Fin 4) := w31 ++ w15
def w42 : List (Fin 4) := w4 ++ w1
def w43 : List (Fin 4) := w8 ++ w9
def w44 : List (Fin 4) := w10 ++ w36
def w45 : List (Fin 4) := w16 ++ w17
def w46 : List (Fin 4) := w45 ++ w14
def w47 : List (Fin 4) := w38 ++ w5
def w48 : List (Fin 4) := w12 ++ w32
def w49 : List (Fin 4) := w13 ++ w18
def w50 : List (Fin 4) := w41 ++ w6
def w51 : List (Fin 4) := w50 ++ w15
def w52 : List (Fin 4) := w51 ++ w7
def w53 : List (Fin 4) := w52 ++ w26
def w54 : List (Fin 4) := w53 ++ w16
def w55 : List (Fin 4) := w54 ++ w8
def w56 : List (Fin 4) := w55 ++ w14
def w57 : List (Fin 4) := w56 ++ w39
def w58 : List (Fin 4) := w12 ++ w4
def w59 : List (Fin 4) := w4 ++ w16
def w60 : List (Fin 4) := w9 ++ w5
def w61 : List (Fin 4) := w4 ++ w5
def w62 : List (Fin 4) := w6 ++ w10
def w63 : List (Fin 4) := w24 ++ w25
def w64 : List (Fin 4) := w16 ++ w12
def w65 : List (Fin 4) := w64 ++ w30
def w66 : List (Fin 4) := w10 ++ w2
def w67 : List (Fin 4) := w66 ++ w13
def w68 : List (Fin 4) := w67 ++ w7
def w69 : List (Fin 4) := w68 ++ w35
def w70 : List (Fin 4) := w69 ++ w22
def w71 : List (Fin 4) := w70 ++ w44
def w72 : List (Fin 4) := w71 ++ w46
def w73 : List (Fin 4) := w72 ++ w8
def w74 : List (Fin 4) := w73 ++ w23
def w75 : List (Fin 4) := w74 ++ w13
def w76 : List (Fin 4) := w75 ++ w37
def w77 : List (Fin 4) := w76 ++ w47
def w78 : List (Fin 4) := w77 ++ w19
def w79 : List (Fin 4) := w78 ++ w48
def w80 : List (Fin 4) := w79 ++ w0
def w81 : List (Fin 4) := w80 ++ w48
def w82 : List (Fin 4) := w81 ++ w5
def w83 : List (Fin 4) := w82 ++ w20
def w84 : List (Fin 4) := w83 ++ w26
def w85 : List (Fin 4) := w84 ++ w15
def w86 : List (Fin 4) := w85 ++ w12
def w87 : List (Fin 4) := w86 ++ w38
def w88 : List (Fin 4) := w87 ++ w39
def w89 : List (Fin 4) := w40 ++ w25
def w90 : List (Fin 4) := w89 ++ w20
def w91 : List (Fin 4) := w90 ++ w33
def w92 : List (Fin 4) := w91 ++ w37
def w93 : List (Fin 4) := w92 ++ w49
def w94 : List (Fin 4) := w93 ++ w8
def w95 : List (Fin 4) := w94 ++ w19
def w96 : List (Fin 4) := w95 ++ w19
def w97 : List (Fin 4) := w96 ++ w8
def w98 : List (Fin 4) := w97 ++ w5
def w99 : List (Fin 4) := w98 ++ w23
def w100 : List (Fin 4) := w99 ++ w15
def w101 : List (Fin 4) := w100 ++ w33
def w102 : List (Fin 4) := w101 ++ w15
def w103 : List (Fin 4) := w102 ++ w31
def w104 : List (Fin 4) := w103 ++ w2
def w105 : List (Fin 4) := w104 ++ w57
def w106 : List (Fin 4) := w40 ++ w11
def w107 : List (Fin 4) := w106 ++ w12
def w108 : List (Fin 4) := w107 ++ w9
def w109 : List (Fin 4) := w108 ++ w32
def w110 : List (Fin 4) := w109 ++ w58
def w111 : List (Fin 4) := w110 ++ w11
def w112 : List (Fin 4) := w111 ++ w22
def w113 : List (Fin 4) := w112 ++ w35
def w114 : List (Fin 4) := w113 ++ w10
def w115 : List (Fin 4) := w114 ++ w34
def w116 : List (Fin 4) := w115 ++ w9
def w117 : List (Fin 4) := w116 ++ w42
def w118 : List (Fin 4) := w117 ++ w33
def w119 : List (Fin 4) := w118 ++ w7
def w120 : List (Fin 4) := w119 ++ w22
def w121 : List (Fin 4) := w120 ++ w22
def w122 : List (Fin 4) := w121 ++ w7
def w123 : List (Fin 4) := w122 ++ w59
def w124 : List (Fin 4) := w123 ++ w24
def w125 : List (Fin 4) := w124 ++ w57
def w126 : List (Fin 4) := w25 ++ w37
def w127 : List (Fin 4) := w126 ++ w60
def w128 : List (Fin 4) := w127 ++ w3
def w129 : List (Fin 4) := w128 ++ w26
def w130 : List (Fin 4) := w129 ++ w18
def w131 : List (Fin 4) := w130 ++ w1
def w132 : List (Fin 4) := w131 ++ w9
def w133 : List (Fin 4) := w132 ++ w8
def w134 : List (Fin 4) := w133 ++ w59
def w135 : List (Fin 4) := w134 ++ w9
def w136 : List (Fin 4) := w135 ++ w14
def w137 : List (Fin 4) := w136 ++ w9
def w138 : List (Fin 4) := w137 ++ w61
def w139 : List (Fin 4) := w138 ++ w0
def w140 : List (Fin 4) := w139 ++ w34
def w141 : List (Fin 4) := w140 ++ w43
def w142 : List (Fin 4) := w141 ++ w3
def w143 : List (Fin 4) := w142 ++ w41
def w144 : List (Fin 4) := w143 ++ w32
def w145 : List (Fin 4) := w144 ++ w9
def w146 : List (Fin 4) := w145 ++ w16
def w147 : List (Fin 4) := w146 ++ w61
def w148 : List (Fin 4) := w147 ++ w3
def w149 : List (Fin 4) := w148 ++ w11
def w150 : List (Fin 4) := w149 ++ w49
def w151 : List (Fin 4) := w150 ++ w1
def w152 : List (Fin 4) := w151 ++ w16
def w153 : List (Fin 4) := w152 ++ w20
def w154 : List (Fin 4) := w153 ++ w35
def w155 : List (Fin 4) := w154 ++ w13
def w156 : List (Fin 4) := w155 ++ w10
def w157 : List (Fin 4) := w156 ++ w13
def w158 : List (Fin 4) := w1 ++ w62
def w159 : List (Fin 4) := w158 ++ w3
def w160 : List (Fin 4) := w159 ++ w43
def w161 : List (Fin 4) := w160 ++ w8
def w162 : List (Fin 4) := w161 ++ w63
def w163 : List (Fin 4) := w162 ++ w11
def w164 : List (Fin 4) := w163 ++ w7
def w165 : List (Fin 4) := w164 ++ w2
def w166 : List (Fin 4) := w165 ++ w36
def w167 : List (Fin 4) := w166 ++ w46
def w168 : List (Fin 4) := w167 ++ w42
def w169 : List (Fin 4) := w168 ++ w31
def w170 : List (Fin 4) := w169 ++ w44
def w171 : List (Fin 4) := w170 ++ w9
def w172 : List (Fin 4) := w171 ++ w63
def w173 : List (Fin 4) := w172 ++ w7
def w174 : List (Fin 4) := w173 ++ w15
def w175 : List (Fin 4) := w174 ++ w25
def w176 : List (Fin 4) := w175 ++ w3
def w177 : List (Fin 4) := w176 ++ w65
def w178 : List (Fin 4) := w40 ++ w20
def w179 : List (Fin 4) := w178 ++ w15
def w180 : List (Fin 4) := w179 ++ w62
def w181 : List (Fin 4) := w180 ++ w8
def w182 : List (Fin 4) := w181 ++ w17
def w183 : List (Fin 4) := w182 ++ w34
def w184 : List (Fin 4) := w183 ++ w12
def w185 : List (Fin 4) := w184 ++ w23
def w186 : List (Fin 4) := w185 ++ w12
def w187 : List (Fin 4) := w186 ++ w8
def w188 : List (Fin 4) := w187 ++ w47
def w189 : List (Fin 4) := w188 ++ w17
def w190 : List (Fin 4) := w189 ++ w58
def w191 : List (Fin 4) := w190 ++ w0
def w192 : List (Fin 4) := w191 ++ w60
def w193 : List (Fin 4) := w192 ++ w17
def w194 : List (Fin 4) := w193 ++ w42
def w195 : List (Fin 4) := w194 ++ w11
def w196 : List (Fin 4) := w195 ++ w13
def w197 : List (Fin 4) := w196 ++ w33
def w198 : List (Fin 4) := w197 ++ w14
def w199 : List (Fin 4) := w198 ++ w43
def w200 : List (Fin 4) := w199 ++ w0
def w201 : List (Fin 4) := w200 ++ w65

def finalWord : Fin 6 → List (Fin 4) := ![w88, w105, w125, w157, w177, w201]

theorem finalWord_eq : ∀ i, finalWord i = word i := by decide +kernel

end LiftWords

/-- Left kernel corrections for the six literal representatives. -/
def correction : Fin 6 → ℕ := ![1472, 544, 1764, 1824, 672, 576]

/-- The original Mathieu kernel element with the indicated binary coordinates. -/
def nativeMask (m : ℕ) : SylowCore.Local :=
  Simplicity.Max1Fusion.KernelOrbits.maskValue matrixA_mul_self matrixB_pow_four m

/-- Corrected native representatives. Their relations are proved by matrix certificates. -/
def correctedLift (i : Fin 6) : SylowCore.Local :=
  nativeMask (correction i) * permutationLift i

end Janko4.LocalStructure.ElementaryEightGeometry
