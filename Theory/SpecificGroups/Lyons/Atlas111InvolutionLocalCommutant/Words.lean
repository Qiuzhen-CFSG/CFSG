module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Reduction
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Words.Product00
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Words.Product01
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Words.Product02
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Words.Product03
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Words.Product04
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Words.Product05
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Words.Product06
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Words.Product07
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Words.Product08
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Words.Product09
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Words.Product10
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Words.Product11
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Words.Product12
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Words.Product13
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Words.Product14
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Words.Product15
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Words.Product16

/-!
# Packed matrices for the literal Lyons local generators

The first output of `LyG1-max4W1` is `ab`, the proposed involution is `(ab)⁷`,
and the second output is evaluated by the certified straight-line products.
A checked left inverse justifies the inverse occurring in that program.
The two final product certificates prove that local B commutes with the involution.

Adapted from the retained `Atlas111InvolutionWords.lean` and its Data/Product00–16
certificates. Source: R. A. Wilson et al., ATLAS of Finite Group Representations;
original matrices and attribution are in `Atlas111Source/`, and the literal
subgroup program and attribution are in `Atlas111InvolutionSource/`.
`Words/source/GenerateWords.py` reproduces the candidates; all checks run in Lean.
-/

namespace Lyons.SimplicityCertificate.LocalCommutant.Words

open Atlas111WordCertificate

private theorem square_power {M : Type*} [Monoid M] (x y z : M) (n : ℕ)
    (h : x ^ n = y) (hm : y * y = z) : x ^ (n * 2) = z :=
  (pow_mul x n 2).trans ((congrArg (fun t : M => t ^ 2) h).trans
    ((pow_two y).trans hm))

private theorem step_power {M : Type*} [Monoid M] (x y z : M) (n : ℕ)
    (h : x ^ n = y) (hm : y * x = z) : x ^ (n + 1) = z :=
  (pow_succ x n).trans ((congrArg (fun t : M => t * x) h).trans hm)

private theorem representation_inv {G M : Type*} [Group G] [Monoid M]
    (f : G →* M) (g : G) (m : M)
    (h : m * f g = 1) : f g⁻¹ = m := by
  have hi : f g * f g⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  exact (left_inv_eq_right_inv h hi).symm

private theorem image_ab :
    matrixRepresentation (generatorA * generatorB) = abMatrix := by
  rw [map_mul, matrixRepresentation_generatorA, matrixRepresentation_generatorB,
    ← aMatrix_eq, ← bMatrix_eq, mul_ab]

/-- The proposed involution is the decoded seventh power of `ab`. -/
public theorem image_t : matrixRepresentation involutionLocalT = ab7Matrix := by
  have h2 : abMatrix ^ 2 = ab2Matrix := (pow_two _).trans mul_ab2
  have h3 : abMatrix ^ 3 = ab3Matrix := by
    simpa only [Nat.reduceAdd] using step_power _ _ _ 2 h2 mul_ab3
  have h6 : abMatrix ^ 6 = ab6Matrix := by
    simpa only [Nat.reduceMul] using square_power _ _ _ 3 h3 mul_ab6
  have h7 : abMatrix ^ 7 = ab7Matrix := by
    simpa only [Nat.reduceAdd] using step_power _ _ _ 6 h6 mul_ab7
  rw [involutionLocalT, map_pow, image_ab, h7]

private def localR10 : LyonsGroup :=
  let r3 := generatorA * generatorB
  let r4 := r3 * generatorB
  let r5 := r3 * r4
  let r6 := r3 * r5
  let r8 := r6 * r5
  let r9 := r3 * r8
  r9 * r4

private def localC : LyonsGroup :=
  (localR10 * involutionLocalT)⁻¹ * (involutionLocalT * localR10)

private theorem localB_eq : involutionLocalB = localR10 * localC ^ 10 := rfl

private theorem image_r10 : matrixRepresentation localR10 = r10Matrix := by
  simp only [localR10, map_mul, matrixRepresentation_generatorA,
    matrixRepresentation_generatorB, ← aMatrix_eq, ← bMatrix_eq,
    mul_ab, mul_r4, mul_r5, mul_r6, mul_r8, mul_r9, mul_r10]

private theorem image_c : matrixRepresentation localC = cMatrix := by
  have hi : matrixRepresentation (localR10 * involutionLocalT)⁻¹ = rtInvMatrix := by
    apply representation_inv matrixRepresentation
    rw [map_mul, image_r10, image_t, mul_rt, mul_rtInvCheck, oneMatrix_eq]
  rw [localC, map_mul, hi, map_mul, image_t, image_r10, mul_tr, mul_c]

/-- The literal second output of `LyG1-max4W1` is the decoded local-B matrix. -/
public theorem image_localB : matrixRepresentation involutionLocalB = localBMatrix := by
  have h2 : cMatrix ^ 2 = c2Matrix := (pow_two _).trans mul_c2
  have h4 : cMatrix ^ 4 = c4Matrix := by
    simpa only [Nat.reduceMul] using square_power _ _ _ 2 h2 mul_c4
  have h5 : cMatrix ^ 5 = c5Matrix := by
    simpa only [Nat.reduceAdd] using step_power _ _ _ 4 h4 mul_c5
  have h10 : cMatrix ^ 10 = c10Matrix := by
    simpa only [Nat.reduceMul] using square_power _ _ _ 5 h5 mul_c10
  rw [localB_eq, map_mul, image_r10, map_pow, image_c, h10, mul_localB]

/-- The literal first output is the decoded product of the standard generators. -/
public theorem image_localA : matrixRepresentation involutionLocalA = abMatrix := by
  rw [involutionLocalA_eq, image_ab]

/-- Every radix-3125 digit of a local-B row is a canonical element of `ZMod 5`. -/
public theorem localB_digit_lt (i j : Fin 111) : digit (localBRows i) j.val < 5 :=
  (small_sound _ _ (localB_small i)).2 j.val j.isLt

/-- A local-B row occupies at most 111 radix-3125 digits. -/
public theorem localB_row_lt (i : Fin 111) : localBRows i < radix ^ 111 :=
  (small_sound _ _ (localB_small i)).1

/-- Decoding the packed local-B rows gives its certified matrix. -/
public theorem localBMatrix_eq_decode : localBMatrix = decode localBRows := rfl

/-- The two certified products have the same decoded result. -/
public theorem localBMatrix_commutes : Commute localBMatrix ab7Matrix :=
  mul_bt.trans mul_tb.symm

/-- Commutation transported to the literal represented words. -/
public theorem image_localB_commutes :
    Commute (matrixRepresentation involutionLocalB) (matrixRepresentation involutionLocalT) := by
  rw [image_localB, image_t]
  exact localBMatrix_commutes

/-- The first generator commutes with the involution, which is its seventh power. -/
public theorem image_localA_commutes :
    Commute (matrixRepresentation involutionLocalA) (matrixRepresentation involutionLocalT) := by
  change matrixRepresentation involutionLocalA * matrixRepresentation involutionLocalT =
    matrixRepresentation involutionLocalT * matrixRepresentation involutionLocalA
  rw [← map_mul, involutionLocalA_commutes, map_mul]

end Lyons.SimplicityCertificate.LocalCommutant.Words
