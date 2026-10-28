module

public import Theory.SpecificGroups.Thompson.Model.GeneratorCertificates.BinaryMatrix
public import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic.FinCases
/-!
# A checked rank-one certificate for the point action

The matrices use the augmentation basis `eᵢ + e₁₂`, with rows packed into
natural numbers. Every product is checked by the binary matrix checker and
all finite equalities are proved by kernel reduction. Put
`M = A₁ A₁ A₀ A₁ + A₁`. The polynomial
`M¹¹ + M⁹ + M⁸ + M⁷ + M⁶ + M⁵ + M⁴ + M³ + 1`
is an outer product `c r`. Twelve short actor words give a basis from `c`
and a basis of the dual space from `r`; the displayed inverse matrices certify spanning.

These data come from the native projective action, not a character table or
an assumed group presentation. The action correspondence is proved in the
parent PointSimplicity module. Source application: Guralnick--Malle,
*Classification of 2F-modules I*, Proposition 4.2, manuscript pp.9--10.
-/

@[expose] public section

open scoped BigOperators Matrix
open Thompson.BinaryMatrix
namespace Representation.PSL3Three.AbsoluteDegrees.PrincipalModels.PointSimplicity
abbrev Mat := Matrix (Fin 12) (Fin 12) (ZMod 2)
def actorRows : Fin 2 → Array ℕ := ![#[1, 1024, 4095, 2048, 16, 32, 64, 2, 4, 8, 128, 512], #[2, 16, 128, 1024, 1, 4, 8, 32, 256, 2048, 64, 4095]]
def A (i : Fin 2) : Mat := decode 12 (actorRows i)
def w0 : Mat := decode 12 #[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]
lemma w0_eq : w0 = 1 := by decide +kernel
def w1 : Mat := decode 12 #[1, 1024, 4095, 2048, 16, 32, 64, 2, 4, 8, 128, 512]
lemma w1_eq : w1 = A 0 * w0 := by
  symm
  apply decode_mul
  decide +kernel
def w2 : Mat := decode 12 #[2, 16, 128, 1024, 1, 4, 8, 32, 256, 2048, 64, 4095]
lemma w2_eq : w2 = A 1 * w0 := by
  symm
  apply decode_mul
  decide +kernel
def w3 : Mat := decode 12 #[1, 128, 256, 512, 16, 32, 64, 1024, 4095, 2048, 2, 8]
lemma w3_eq : w3 = A 0 * w1 := by
  symm
  apply decode_mul
  decide +kernel
def w4 : Mat := decode 12 #[2, 64, 512, 4095, 1, 4, 8, 16, 128, 1024, 32, 2048]
lemma w4_eq : w4 = A 0 * w2 := by
  symm
  apply decode_mul
  decide +kernel
def w5 : Mat := decode 12 #[1024, 16, 2, 128, 1, 4095, 2048, 32, 4, 512, 64, 256]
lemma w5_eq : w5 = A 1 * w1 := by
  symm
  apply decode_mul
  decide +kernel
def w6 : Mat := decode 12 #[16, 1, 32, 64, 2, 128, 1024, 4, 256, 4095, 8, 512]
lemma w6_eq : w6 = A 1 * w2 := by
  symm
  apply decode_mul
  decide +kernel
def w7 : Mat := decode 12 #[2, 32, 256, 2048, 1, 4, 8, 64, 512, 4095, 16, 1024]
lemma w7_eq : w7 = A 0 * w4 := by
  symm
  apply decode_mul
  decide +kernel
def w8 : Mat := decode 12 #[1024, 64, 8, 256, 1, 4095, 2048, 16, 2, 128, 32, 512]
lemma w8_eq : w8 = A 0 * w5 := by
  symm
  apply decode_mul
  decide +kernel
def w9 : Mat := decode 12 #[16, 8, 2048, 512, 2, 128, 1024, 1, 32, 64, 4, 4095]
lemma w9_eq : w9 = A 0 * w6 := by
  symm
  apply decode_mul
  decide +kernel
def w10 : Mat := decode 12 #[128, 16, 1024, 2, 1, 256, 512, 32, 4095, 8, 64, 4]
lemma w10_eq : w10 = A 1 * w3 := by
  symm
  apply decode_mul
  decide +kernel
def w11 : Mat := decode 12 #[64, 1, 16, 32, 2, 512, 4095, 4, 128, 2048, 8, 256]
lemma w11_eq : w11 = A 1 * w4 := by
  symm
  apply decode_mul
  decide +kernel
def w12 : Mat := decode 12 #[16, 1, 32, 64, 1024, 2, 128, 4095, 4, 256, 2048, 8]
lemma w12_eq : w12 = A 1 * w5 := by
  symm
  apply decode_mul
  decide +kernel
def w13 : Mat := decode 12 #[128, 64, 2048, 4, 1, 256, 512, 16, 1024, 2, 32, 8]
lemma w13_eq : w13 = A 0 * w10 := by
  symm
  apply decode_mul
  decide +kernel
def w14 : Mat := decode 12 #[32, 1, 64, 16, 2, 256, 2048, 4, 512, 1024, 8, 128]
lemma w14_eq : w14 = A 1 * w7 := by
  symm
  apply decode_mul
  decide +kernel
def w15 : Mat := decode 12 #[8, 2, 1, 4, 16, 2048, 512, 128, 32, 4095, 1024, 256]
lemma w15_eq : w15 = A 1 * w9 := by
  symm
  apply decode_mul
  decide +kernel
def w16 : Mat := decode 12 #[16, 1, 32, 64, 128, 1024, 2, 256, 4095, 4, 512, 2048]
lemma w16_eq : w16 = A 1 * w10 := by
  symm
  apply decode_mul
  decide +kernel
def w17 : Mat := decode 12 #[1, 2, 4, 8, 64, 16, 32, 512, 128, 256, 4095, 1024]
lemma w17_eq : w17 = A 1 * w11 := by
  symm
  apply decode_mul
  decide +kernel
def M : Mat := decode 12 #[3, 18, 132, 1032, 65, 20, 40, 544, 384, 2304, 4031, 3071]
lemma M_eq : M = w17 + w2 := by decide +kernel
def p0 : Mat := decode 12 #[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]
lemma p0_eq : p0 = 1 := by decide +kernel
def p1 : Mat := decode 12 #[3, 18, 132, 1032, 65, 20, 40, 544, 384, 2304, 4031, 3071]
lemma p1_eq : p1 = p0 * M := by
  have h : p0 * M = decode 12 #[3, 18, 132, 1032, 65, 20, 40, 544, 384, 2304, 4031, 3071] := by
    apply decode_mul
    decide +kernel
  rw [h]
  decide +kernel
def p2 : Mat := decode 12 #[16, 81, 672, 3007, 59, 229, 1116, 2452, 672, 2175, 3624, 3519]
lemma p2_eq : p2 = p1 * M + 1 := by
  have h : p1 * M = decode 12 #[17, 83, 676, 2999, 43, 197, 1052, 2324, 928, 2687, 2600, 1471] := by
    apply decode_mul
    decide +kernel
  rw [h]
  decide +kernel
def p3 : Mat := decode 12 #[64, 104, 2864, 1439, 1116, 699, 2842, 2074, 2612, 3359, 3420, 2856]
lemma p3_eq : p3 = p2 * M + 1 := by
  have h : p2 * M = decode 12 #[65, 106, 2868, 1431, 1100, 667, 2906, 2202, 2868, 3871, 2396, 808] := by
    apply decode_mul
    decide +kernel
  rw [h]
  decide +kernel
def p4 : Mat := decode 12 #[41, 1078, 814, 2251, 2890, 3916, 1892, 3876, 814, 796, 1317, 3939]
lemma p4_eq : p4 = p3 * M + 1 := by
  have h : p3 * M = decode 12 #[40, 1076, 810, 2243, 2906, 3948, 1828, 4004, 558, 284, 293, 1891] := by
    apply decode_mul
    decide +kernel
  rw [h]
  decide +kernel
def p5 : Mat := decode 12 #[1054, 3966, 3086, 3558, 1885, 2116, 1991, 3280, 3338, 3661, 2732, 1261]
lemma p5_eq : p5 = p4 * M + 1 := by
  have h : p4 * M = decode 12 #[1055, 3964, 3082, 3566, 1869, 2148, 1927, 3152, 3082, 3149, 3756, 3309] := by
    apply decode_mul
    decide +kernel
  rw [h]
  decide +kernel
def p6 : Mat := decode 12 #[2913, 2081, 218, 1858, 969, 2931, 1506, 1673, 218, 3047, 71, 300]
lemma p6_eq : p6 = p5 * M + 1 := by
  have h : p5 * M = decode 12 #[2912, 2083, 222, 1866, 985, 2899, 1442, 1545, 474, 2535, 1095, 2348] := by
    apply decode_mul
    decide +kernel
  rw [h]
  decide +kernel
def p7 : Mat := decode 12 #[833, 3050, 1623, 1805, 3731, 819, 3185, 20, 1875, 1014, 1213, 3352]
lemma p7_eq : p7 = p6 * M + 1 := by
  have h : p6 * M = decode 12 #[832, 3048, 1619, 1797, 3715, 787, 3121, 148, 1619, 502, 189, 1304] := by
    apply decode_mul
    decide +kernel
  rw [h]
  decide +kernel
def p8 : Mat := decode 12 #[2218, 1403, 1607, 952, 3872, 2276, 1150, 69, 1607, 2123, 3397, 2441]
lemma p8_eq : p8 = p7 * M + 1 := by
  have h : p7 * M = decode 12 #[2219, 1401, 1603, 944, 3888, 2244, 1086, 197, 1863, 2635, 2373, 393] := by
    apply decode_mul
    decide +kernel
  rw [h]
  decide +kernel
def p9 : Mat := decode 12 #[3537, 2651, 1538, 3837, 3284, 2407, 2908, 175, 1538, 4046, 1391, 3156]
lemma p9_eq : p9 = p8 * M := by
  have h : p8 * M = decode 12 #[3537, 2651, 1538, 3837, 3284, 2407, 2908, 175, 1538, 4046, 1391, 3156] := by
    apply decode_mul
    decide +kernel
  rw [h]
  decide +kernel
def p10 : Mat := decode 12 #[1930, 1679, 1709, 2962, 1677, 2774, 1946, 1705, 1709, 2646, 2718, 1197]
lemma p10_eq : p10 = p9 * M := by
  have h : p9 * M = decode 12 #[1930, 1679, 1709, 2962, 1677, 2774, 1946, 1705, 1709, 2646, 2718, 1197] := by
    apply decode_mul
    decide +kernel
  rw [h]
  decide +kernel
def p11 : Mat := decode 12 #[260, 0, 0, 260, 0, 0, 260, 0, 260, 0, 0, 260]
lemma p11_eq : p11 = p10 * M + 1 := by
  have h : p10 * M = decode 12 #[261, 2, 4, 268, 16, 32, 324, 128, 4, 512, 1024, 2308] := by
    apply decode_mul
    decide +kernel
  rw [h]
  decide +kernel
def c : Fin 12 → ZMod 2 := fun i => bit 2377 i.val
def r : Fin 12 → ZMod 2 := fun i => bit 260 i.val
lemma rank_one : p11 = Matrix.vecMulVec c r := by decide +kernel
def C : Mat := decode 12 #[11, 3744, 2826, 1443, 884, 2640, 2367, 1408, 1101, 462, 2260, 1725]
def D : Mat := decode 12 #[260, 4091, 384, 640, 6, 288, 10, 2080, 3071, 144, 576, 33]
def Cinv : Mat := decode 12 #[911, 15, 1735, 897, 113, 776, 2206, 1170, 2885, 1653, 3927, 3770]
def Dinv : Mat := decode 12 #[1985, 4080, 4064, 4016, 3557, 4033, 3053, 4069, 4065, 4077, 3810, 3905]
lemma C_inverse : C * Cinv = 1 := by
  apply decode_mul_one
  decide +kernel
lemma D_inverse : Dinv * D = 1 := by
  apply decode_mul_one
  decide +kernel
def leftWords : Fin 12 → Mat := ![w0, w1, w2, w3, w5, w4, w10, w12, w7, w13, w16, w14]
def rightWords : Fin 12 → Mat := ![w0, w1, w2, w4, w5, w6, w8, w9, w10, w11, w14, w15]
set_option backward.isDefEq.respectTransparency false in
lemma columns : C = fun i j => (leftWords j *ᵥ c) i := by decide +kernel
set_option backward.isDefEq.respectTransparency false in
lemma rows : D = fun i j => (r ᵥ* rightWords i) j := by decide +kernel
end Representation.PSL3Three.AbsoluteDegrees.PrincipalModels.PointSimplicity
