module

public import Theory.SpecificGroups.Triality.RadicalCoordinates.FullLeviDefinitions
public import Theory.SpecificGroups.Triality.ConcreteBruhat.Torus

/-!
# Torus normalization of the triality subsystem Levis

The negative simple Geck operator lowers lattice weights by its simple root.
Its integral factorial identities extend this support calculation to every
divided power. The proved coroot diagonals therefore scale negative as well as
positive simple curves. Conjugation preserves the generators of either
subsystem Levi, and relative normality descends through elementary fixed
points and the central quotient.

Source: GLS3 §§2.4, 2.6, especially Theorem 2.6.5(f)
(`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section

open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open Triality.Standard.PositiveCoordinates.Injectivity
namespace Triality.Standard.RadicalCoordinates
open Parabolics ConcreteBruhat TorusCoordinates Parabolics.RankOneMatrices
noncomputable section
local instance : DecidableEq LatticeIndex := fun a b => instDecidableEqSum a b

private lemma f_homogeneous (j : Fin 4) :
    Homogeneous (rootWeight (b := typeDRootPairing_base 2))
      (fMatrix (typeDRootPairing_baseEquiv 2 j))
      (-(typeDRootPairing 2).root (typeDSimpleRootIndex 2 j)) := by
  classical
  let i := typeDRootPairing_baseEquiv 2 j
  let := (typeDRootPairing 2).indexNeg
  intro a b hab
  rcases a with a | a <;> rcases b with b | b
  · simp [fMatrix] at hab
  · have h : a = i ∧ b = i := by
      by_contra h
      exact hab (by change (if a = i ∧ b = i then (1 : ℤ) else 0) = 0; rw [if_neg h])
    simp [rootWeight, h.2, i]
  · have h : a = -i := by
      by_contra h
      exact hab (by change (if a = -i then _ else 0) = 0; rw [if_neg h])
    change (typeDRootPairing 2).root a = -(typeDRootPairing 2).root i + 0
    rw [h, add_zero]
    change (typeDRootPairing 2).root ((typeDRootPairing 2).reflectionPerm i i) = _
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
  · have h : (typeDRootPairing 2).root a = (typeDRootPairing 2).root b - (typeDRootPairing 2).root i := by
      by_contra h
      apply hab
      dsimp only [fMatrix, Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
      dsimp only [i] at h
      rw [if_neg h]
    simpa [rootWeight, sub_eq_neg_add, i] using h

private lemma f_power_homogeneous (j : Fin 4) (n : ℕ) :
    Homogeneous (rootWeight (b := typeDRootPairing_base 2))
      (fDividedPower (typeDRootPairing_baseEquiv 2 j) n)
      (n • (-(typeDRootPairing 2).root (typeDSimpleRootIndex 2 j))) := by
  have h := homogeneous_pow _ (f_homogeneous j) n
  intro a b hab
  apply h a b
  rw [fMatrix_pow_eq_factorial_smul]
  change (n.factorial : ℤ) * _ ≠ 0
  exact mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero n) hab

private lemma weight_cast (i : Fin 4) (k : LatticeIndex) :
    ((corootWeight i k : ℤ) : ℝ) =
      (typeDRootPairing 2).coroot' (typeDSimpleRootIndex 2 i)
        (rootWeight (b := typeDRootPairing_base 2) k) := by
  rcases k with k | k
  · simp [corootWeight, rootWeight]
  · change ((typeDRootPairing 2).pairingIn ℤ k (typeDSimpleRootIndex 2 i) : ℝ) =
      (typeDRootPairing 2).coroot' (typeDSimpleRootIndex 2 i) ((typeDRootPairing 2).root k)
    rw [RootPairing.root_coroot'_eq_pairing]
    exact (typeDRootPairing 2).algebraMap_pairingIn ℤ k (typeDSimpleRootIndex 2 i)

private lemma negative_weight_support (i j : Fin 4) (n : ℕ) (a b : LatticeIndex)
    (hab : fDividedPower (typeDRootPairing_baseEquiv 2 j) n a b ≠ 0) :
    corootWeight i a = n * (-typeDCartanMatrix 2 j i) + corootWeight i b := by
  have h := congrArg ((typeDRootPairing 2).coroot' (typeDSimpleRootIndex 2 i))
    (f_power_homogeneous j n a b hab)
  rw [map_add, map_nsmul, map_neg, ← weight_cast, ← weight_cast,
    RootPairing.root_coroot'_eq_pairing,
    ← (typeDRootPairing 2).algebraMap_pairingIn ℤ] at h
  simp only [nsmul_eq_mul, eq_intCast] at h
  have hc : (typeDRootPairing 2).pairingIn ℤ
      (typeDSimpleRootIndex 2 j) (typeDSimpleRootIndex 2 i) = typeDCartanMatrix 2 j i :=
    typeDRootPairing_base_cartanMatrix 2 j i
  rw [hc] at h
  exact_mod_cast h

private lemma negative_diagonal_term (P : Parameters) (i : Fin 4)
    (t : (ExtensionField P)ˣ) (j : Fin 4) (n : ℕ) (s : ExtensionField P) :
    corootDiagonal P i t *
      (s ^ n • specializeMatrix (fDividedPower (typeDRootPairing_baseEquiv 2 j) n)) =
      ((t.val ^ (-typeDCartanMatrix 2 j i) * s) ^ n •
        specializeMatrix (fDividedPower (typeDRootPairing_baseEquiv 2 j) n)) *
          corootDiagonal P i t := by
  ext a b
  simp only [corootDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.smul_apply, smul_eq_mul, specializeMatrix, Matrix.map_apply]
  by_cases h : fDividedPower (typeDRootPairing_baseEquiv 2 j) n a b = 0
  · simp [h]
  · rw [negative_weight_support i j n a b h, zpow_add₀ t.ne_zero,
      mul_comm (n : ℤ), zpow_mul, zpow_natCast, mul_pow]
    ring

theorem torusWord_negativeRoot_conjugate (P : Parameters) (hp : P.prime = 2)
    (i : Fin 4) (t : (ExtensionField P)ˣ) (j : Fin 4) (s : ExtensionField P) :
    torusWord P i t * negativeRoot P j s * (torusWord P i t)⁻¹ =
      negativeRoot P j (t.val ^ (-typeDCartanMatrix 2 j i) * s) := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply Subtype.ext
  apply Units.ext
  change (torusWord P i t).val.val * _ = _ * (torusWord P i t).val.val
  rw [torusWord_val P hp]
  change corootDiagonal P i t * (RootPairing.SimpleGeckGroup.negativeMatrix _ s) =
    RootPairing.SimpleGeckGroup.negativeMatrix _ _ * corootDiagonal P i t
  simp only [RootPairing.SimpleGeckGroup.negativeMatrix_formula]
  change corootDiagonal P i t * (1 + s • specializeMatrix (fDividedPower _ 1) +
    s ^ 2 • specializeMatrix (fDividedPower _ 2) + s ^ 3 • specializeMatrix (fDividedPower _ 3)) =
    (1 + _ • specializeMatrix (fDividedPower _ 1) +
    _ ^ 2 • specializeMatrix (fDividedPower _ 2) + _ ^ 3 • specializeMatrix (fDividedPower _ 3)) * corootDiagonal P i t
  simp only [mul_add, add_mul, mul_one, one_mul]
  rw [negative_diagonal_term P i t j 2, negative_diagonal_term P i t j 3]
  have h1 := negative_diagonal_term P i t j 1 s
  simp only [pow_one] at h1
  rw [h1]


theorem torusWord_positiveRoot_conjugate_cartan (P : Parameters) (hp : P.prime = 2)
    (i : Fin 4) (t : (ExtensionField P)ˣ) (j : Fin 4) (s : ExtensionField P) :
    torusWord P i t * positiveRoot P j s * (torusWord P i t)⁻¹ =
      positiveRoot P j (t.val ^ (typeDCartanMatrix 2 j i) * s) := by
  simpa only [show (typeDRootPairing 2).pairingIn ℤ
      (typeDSimpleRootIndex 2 j) (typeDSimpleRootIndex 2 i) = typeDCartanMatrix 2 j i from
        typeDRootPairing_base_cartanMatrix 2 j i] using
    torusWord_positiveRoot_conjugate P hp i t j s

theorem splitTorus_le_normalizer_splitLevi (P : Parameters) (hp : P.prime = 2) (a : Node) :
    splitTorus P ≤ Subgroup.normalizer (splitLevi P a) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, t, rfl⟩
  apply Subgroup.normalizer_le_normalizer_closure
  apply Subgroup.mem_normalizer_iff_conj_image_eq.mpr
  apply Set.Subset.antisymm
  · rintro _ ⟨g, ⟨j, hj, s, rfl | rfl⟩, rfl⟩
    · exact ⟨j, hj, _, Or.inl (torusWord_positiveRoot_conjugate_cartan P hp i t j s)⟩
    · exact ⟨j, hj, _, Or.inr (torusWord_negativeRoot_conjugate P hp i t j s)⟩
  · rintro _ ⟨j, hj, s, rfl | rfl⟩
    · let c := t.val ^ (typeDCartanMatrix 2 j i)
      refine ⟨positiveRoot P j (c⁻¹ * s), ⟨j, hj, _, Or.inl rfl⟩, ?_⟩
      change torusWord P i t * _ * (torusWord P i t)⁻¹ = _
      rw [torusWord_positiveRoot_conjugate_cartan P hp]
      change positiveRoot P j (c * (c⁻¹ * s)) = _
      rw [← mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ t.ne_zero), one_mul]
    · let c := t.val ^ (-typeDCartanMatrix 2 j i)
      refine ⟨negativeRoot P j (c⁻¹ * s), ⟨j, hj, _, Or.inr rfl⟩, ?_⟩
      change torusWord P i t * _ * (torusWord P i t)⁻¹ = _
      rw [torusWord_negativeRoot_conjugate P hp]
      change negativeRoot P j (c * (c⁻¹ * s)) = _
      rw [← mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ t.ne_zero), one_mul]

theorem torus_le_normalizer_levi (P : Parameters) (hp : P.prime = 2) (a : Node) :
    torus P ≤ Subgroup.normalizer (levi P a) := by
  have hL : splitLevi P a ≤ splitFullLevi P a := le_sup_left
  have hN : ((splitLevi P a).subgroupOf (splitFullLevi P a)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL).mpr
      (sup_le (splitLevi P a).le_normalizer (splitTorus_le_normalizer_splitLevi P hp a))
  have hDN := descendSubgroup_normal P hL hN
  exact (descendSubgroup_mono P (show splitTorus P ≤ splitFullLevi P a from le_sup_right)).trans
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (descendSubgroup_mono P hL)).mp hDN)

end
end Triality.Standard.RadicalCoordinates
