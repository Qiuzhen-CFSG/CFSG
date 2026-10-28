module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionCentralizerSetup
public import Theory.SpecificGroups.Lyons.Atlas111WordRelations
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Product00
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Product01
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Product02
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Product03
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Product04
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Product05
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Product06
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Product07
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Product08
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Product09
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Product10
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Product11
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Product12
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Product13
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Product14
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Product15
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Product16
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Product17
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Product18
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Product19
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Product20
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Product21
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Product22
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Product23
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Product24
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Product25
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Product26
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Product27
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Product28
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Product29

/-!
# Concrete involution subgroup word certificates

The exact second output of `LyG1-max4W1` commutes with `(ab)⁷`, and the
transporter specified in the setup conjugates `(ab)⁷` to `a`. We evaluate the
straight-line words through certified matrix products and use faithfulness
of the fixed matrix representation. Inverse candidates are justified by
checked products equal to one; no matrix inversion algorithm is trusted.

Source: the attributed ATLAS matrices in `Atlas111Source/`, the original
subgroup program in `Atlas111InvolutionSource/`, and the reproducible candidate
generator `Atlas111InvolutionSource/GenerateWords.py`.
-/

namespace Lyons.SimplicityCertificate

open Atlas111WordCertificate Atlas111InvolutionWords

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

private theorem image_t : matrixRepresentation involutionLocalT = ab7Matrix := by
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

private theorem image_localB : matrixRepresentation involutionLocalB = localBMatrix := by
  have h2 : cMatrix ^ 2 = c2Matrix := (pow_two _).trans mul_c2
  have h4 : cMatrix ^ 4 = c4Matrix := by
    simpa only [Nat.reduceMul] using square_power _ _ _ 2 h2 mul_c4
  have h5 : cMatrix ^ 5 = c5Matrix := by
    simpa only [Nat.reduceAdd] using step_power _ _ _ 4 h4 mul_c5
  have h10 : cMatrix ^ 10 = c10Matrix := by
    simpa only [Nat.reduceMul] using square_power _ _ _ 5 h5 mul_c10
  rw [localB_eq, map_mul, image_r10, map_pow, image_c, h10, mul_localB]

/-- The two exact subgroup generators both centralize the proposed involution. -/
public theorem involutionLocalB_commutes :
    involutionLocalB * involutionLocalT = involutionLocalT * involutionLocalB := by
  apply matrixRepresentation_injective
  rw [map_mul, map_mul, image_localB, image_t, mul_bt, mul_tb]

private theorem image_seed : matrixRepresentation involutionTransportSeed = seedMatrix := by
  have hs : involutionTransportSeed =
      ((generatorA * generatorB) * generatorB) * (generatorA * generatorB) := by
    simp only [involutionTransportSeed, pow_two, mul_assoc]
  rw [hs, map_mul, map_mul, image_ab, matrixRepresentation_generatorB,
    ← bMatrix_eq, mul_r4, mul_seed]

private theorem image_v :
    matrixRepresentation (generatorA * (involutionTransportSeed⁻¹ * involutionLocalT *
      involutionTransportSeed)) = vMatrix := by
  have hi : matrixRepresentation involutionTransportSeed⁻¹ = seedInvMatrix := by
    apply representation_inv matrixRepresentation
    rw [image_seed, mul_seedInvCheck, oneMatrix_eq]
  rw [map_mul, map_mul, map_mul, matrixRepresentation_generatorA, ← aMatrix_eq,
    hi, image_t, image_seed, mul_seedInvT, mul_u, mul_v]

private theorem image_transporter :
    matrixRepresentation involutionTransporter = transporterMatrix := by
  have h2 : vMatrix ^ 2 = v2Matrix := (pow_two _).trans mul_v2
  have h4 : vMatrix ^ 4 = v4Matrix := by
    simpa only [Nat.reduceMul] using square_power _ _ _ 2 h2 mul_v4
  have h8 : vMatrix ^ 8 = v8Matrix := by
    simpa only [Nat.reduceMul] using square_power _ _ _ 4 h4 mul_v8
  have h9 : vMatrix ^ 9 = v9Matrix := by
    simpa only [Nat.reduceAdd] using step_power _ _ _ 8 h8 mul_v9
  have h18 : vMatrix ^ 18 = v18Matrix := by
    simpa only [Nat.reduceMul] using square_power _ _ _ 9 h9 mul_v18
  rw [involutionTransporter, map_mul, map_pow, image_seed, image_v, h18, mul_transporter]

/-- The explicitly specified transporter has the required conjugation direction. -/
public theorem involutionTransporter_conjugates :
    involutionTransporter⁻¹ * involutionLocalT * involutionTransporter = generatorA := by
  have h : involutionLocalT * involutionTransporter = involutionTransporter * generatorA := by
    apply matrixRepresentation_injective
    rw [map_mul, map_mul, image_t, image_transporter,
      matrixRepresentation_generatorA, ← aMatrix_eq, mul_tw, mul_wa]
  rw [mul_assoc, h, inv_mul_cancel_left]

/-- The concrete ATLAS subgroup lies in the centralizer of its seventh-power word. -/
public theorem involutionLocalSubgroup_le_centralizer_certified :
    involutionLocalSubgroup ≤ Subgroup.centralizer {involutionLocalT} :=
  involutionLocalSubgroup_le_centralizer involutionLocalB_commutes

/-- The seventh-power word is an involution, certified by the word calculation. -/
public theorem involutionLocalT_sq_certified : involutionLocalT ^ 2 = 1 := by
  rw [involutionLocalT, ← pow_mul]
  exact generatorAB_pow_fourteen

/-- The transporter identifies the local word with the nonidentity generator. -/
public theorem involutionLocalT_ne_one : involutionLocalT ≠ 1 := by
  intro h
  have ht := involutionTransporter_conjugates
  rw [h, mul_one, inv_mul_cancel] at ht
  exact generatorA_ne_one ht.symm

/-- The exact local involution has order two. -/
public theorem orderOf_involutionLocalT : orderOf involutionLocalT = 2 :=
  orderOf_eq_prime involutionLocalT_sq_certified involutionLocalT_ne_one

/-- The local involution is central in the concrete generated subgroup. -/
public theorem involutionLocalT_mem_center :
    (⟨involutionLocalT, involutionLocalT_mem⟩ : involutionLocalSubgroup) ∈
      Subgroup.center involutionLocalSubgroup := by
  apply Subgroup.mem_center_iff.mpr
  intro g
  apply Subtype.ext
  exact Subgroup.mem_centralizer_singleton_iff.mp
    (involutionLocalSubgroup_le_centralizer_certified g.property)

/-- The concrete local subgroup is proper, independently of its maximality. -/
public theorem involutionLocalSubgroup_ne_top : involutionLocalSubgroup ≠ ⊤ := by
  intro htop
  have hc (g : LyonsGroup) : g * involutionLocalT = involutionLocalT * g := by
    apply Subgroup.mem_centralizer_singleton_iff.mp
    apply involutionLocalSubgroup_le_centralizer_certified
    rw [htop]
    trivial
  have ht := involutionTransporter_conjugates
  rw [mul_assoc, ← hc involutionTransporter, inv_mul_cancel_left] at ht
  have hb := hc generatorB
  rw [ht] at hb
  exact generators_not_commute hb.symm

end Lyons.SimplicityCertificate
