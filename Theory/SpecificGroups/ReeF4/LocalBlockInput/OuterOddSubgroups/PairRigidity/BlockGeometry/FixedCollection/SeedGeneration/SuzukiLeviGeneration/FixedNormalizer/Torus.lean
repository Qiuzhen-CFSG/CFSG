module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.SeedGeneration.SuzukiLeviGeneration.Basic
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.CorootRealization

/-!
# The full two-coroot torus of the middle F₄ subsystem

The literal words `H₁(a) H₂(b)` have diagonal matrices whose characters at
outer nodes 0 and 3 recover `a⁻¹` and `b⁻¹`. Thus both parameters are unique.
The supplied Ree twist sends `(a,b)` to `(titsEnd(b),theta(a))`, so its fixed
torus is exactly the prescribed `SuzukiGaussData.torusFactor`, for every `m`.

The eight split B₂ representative words and the remaining collection predicate
are published here for the normalizer proof. The predicate retains all nonzero
parameters at both middle nodes; it does not adjoin the complementary torus.

Source: GLS3, 2.3.4–8 and §2.4 (Table 2.4, type V),
`refs/KGroup/GLS3/chapter2.tex`. Coroot matrices use the proved literal-word
realization in `ParabolicAmalgam.Geometry.CorootRealization`.
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
namespace ReeF4.LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration.SuzukiNormalizer
open Parabolics BlockParameters.FieldRecovery LocalIndices.SuzukiGaussData
variable {m : ℕ}

/-- The two independent middle simple-coroot parameters. -/
def torus (a b : (CoefficientField m)ˣ) : SplitGroup m :=
  torusWord m (typeF4SimpleRootIndex 1) a * torusWord m (typeF4SimpleRootIndex 2) b

/-- The eight reduced words in the split B₂ Weyl group. -/
def word : Fin 8 → List (Fin 4) := ![[], [1], [2], [1,2], [2,1], [1,2,1], [2,1,2], [1,2,1,2]]
/-- Literal parameter-one words for the split B₂ representatives. -/
def representative (m : ℕ) (k : Fin 8) : SplitGroup m := Binary.FixedGeometry.simpleWord m (word k)

/-- Collection of arbitrary nonzero normalizer words, with both torus parameters. -/
def SplitForm (m : ℕ) : Prop :=
  ∀ n : SplitGroup m, n ∈ splitSuzukiNormalizer m →
    ∃ a b : (CoefficientField m)ˣ, ∃ k : Fin 8, n = torus a b * representative m k

private theorem basisUnit_simple (i : Fin 4) (u : (CoefficientField m)ˣ)
    (row : F4Chevalley.BasisIndex) :
    chevalleyBasisTorusUnit (P := typeF4RootPairing)
      (integralChevalleySimpleCorootParameter (typeF4RootPairing_baseEquiv i) u) row =
      u ^ (-chevalleyBasisWeight (P := typeF4RootPairing) row (typeF4SimpleRootIndex i)) := by
  unfold chevalleyBasisTorusUnit integralChevalleySimpleCorootParameter
  rw [Finset.prod_eq_single (typeF4RootPairing_baseEquiv i)]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

def scale (a b : (CoefficientField m)ˣ) (row : F4Chevalley.BasisIndex) :
    (CoefficientField m)ˣ :=
  a ^ chevalleyBasisWeight (P := typeF4RootPairing) row (typeF4SimpleRootIndex 1) *
    b ^ chevalleyBasisWeight (P := typeF4RootPairing) row (typeF4SimpleRootIndex 2)

theorem torus_matrix (a b : (CoefficientField m)ˣ) :
    (torus a b).val.val = Matrix.diagonal (fun row => (scale a b row : CoefficientField m)) := by
  change (torusWord m (typeF4SimpleRootIndex 1) a).val.val *
    (torusWord m (typeF4SimpleRootIndex 2) b).val.val = _
  rw [← typeF4RootPairing_baseEquiv_val 1, ← typeF4RootPairing_baseEquiv_val 2,
    torusWord_simple_coe, torusWord_simple_coe]
  change Matrix.diagonal _ * Matrix.diagonal _ = _
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext row
  simp only [basisUnit_simple, inv_zpow, zpow_neg, inv_inv, scale,
    Units.val_mul]

theorem torus_commute (a b c d : (CoefficientField m)ˣ) :
    Commute (torus a b) (torus c d) := by
  change _ * _ = _ * _
  apply Subtype.ext
  apply Units.ext
  change (torus a b).val.val * (torus c d).val.val =
    (torus c d).val.val * (torus a b).val.val
  simp only [torus_matrix, Matrix.diagonal_mul_diagonal, mul_comm]

theorem torus_mul (a b c d : (CoefficientField m)ˣ) :
    torus a b * torus c d = torus (a * c) (b * d) := by
  apply Subtype.ext
  apply Units.ext
  change (torus a b).val.val * (torus c d).val.val = _
  simp only [torus_matrix, Matrix.diagonal_mul_diagonal]
  congr 1
  funext row
  simp only [scale, mul_zpow, Units.val_mul]
  ring

@[simp] theorem torus_one : torus (1 : (CoefficientField m)ˣ) 1 = 1 := by
  apply Subtype.ext
  apply Units.ext
  simpa [scale] using torus_matrix (1 : (CoefficientField m)ˣ) 1

private theorem scale_outer_zero (a b : (CoefficientField m)ˣ) :
    scale a b (.inr (typeF4SimpleRootIndex 0)) = a⁻¹ := by
  simp only [scale, chevalleyBasisWeight]
  have hpair (i j : Fin 4) : typeF4RootPairing.pairingIn ℤ
      (typeF4SimpleRootIndex i) (typeF4SimpleRootIndex j) = typeF4CartanMatrix i j :=
    typeF4RootPairing_base_cartan_apply i j
  rw [hpair, hpair]
  norm_num [typeF4CartanMatrix, Fin.ext_iff]

private theorem scale_outer_three (a b : (CoefficientField m)ˣ) :
    scale a b (.inr (typeF4SimpleRootIndex 3)) = b⁻¹ := by
  simp only [scale, chevalleyBasisWeight]
  have hpair (i j : Fin 4) : typeF4RootPairing.pairingIn ℤ
      (typeF4SimpleRootIndex i) (typeF4SimpleRootIndex j) = typeF4CartanMatrix i j :=
    typeF4RootPairing_base_cartan_apply i j
  rw [hpair, hpair]
  norm_num [typeF4CartanMatrix, Fin.ext_iff]

/-- The two outer root columns recover the independent Levi torus parameters. -/
theorem torus_injective {a b c d : (CoefficientField m)ˣ}
    (h : torus a b = torus c d) : a = c ∧ b = d := by
  have hm := congrArg (fun g : SplitGroup m => g.val.val) h
  rw [torus_matrix, torus_matrix] at hm
  have h0 := congrArg (fun A => A (.inr (typeF4SimpleRootIndex 0))
    (.inr (typeF4SimpleRootIndex 0))) hm
  have h3 := congrArg (fun A => A (.inr (typeF4SimpleRootIndex 3))
    (.inr (typeF4SimpleRootIndex 3))) hm
  simp only [Matrix.diagonal_apply_eq, scale_outer_zero, scale_outer_three] at h0 h3
  exact ⟨inv_injective (Units.ext h0), inv_injective (Units.ext h3)⟩

private theorem coroot_commute (i j : Fin 4) (a b : (CoefficientField m)ˣ) :
    Commute (torusWord m (typeF4SimpleRootIndex i) a)
      (torusWord m (typeF4SimpleRootIndex j) b) := by
  change _ * _ = _ * _
  apply Subtype.ext
  change (torusWord m _ a).val * (torusWord m _ b).val =
    (torusWord m _ b).val * (torusWord m _ a).val
  rw [← typeF4RootPairing_baseEquiv_val i, ← typeF4RootPairing_baseEquiv_val j,
    torusWord_simple_coe, torusWord_simple_coe, ← map_mul, ← map_mul]
  congr 1
  exact mul_comm _ _

private theorem rootFieldEnd_one : rootFieldEnd m (typeF4SimpleRootIndex 1) = theta m := by
  have h : IsLongRoot (typeF4SimpleRootIndex 1) :=
    (typeF4SimpleRootIndex_mem_pair_iff 1).mpr (by decide)
  simp only [rootFieldEnd, if_pos h, theta]
private theorem rootFieldEnd_two : rootFieldEnd m (typeF4SimpleRootIndex 2) = titsEnd m := by
  have h : ¬ IsLongRoot (typeF4SimpleRootIndex 2) := by
    intro h
    have hh := (typeF4SimpleRootIndex_mem_pair_iff 2).mp h
    norm_num at hh
  simp only [rootFieldEnd, if_neg h]

theorem twist_torus (d : LocalBlockInput m) (a b : (CoefficientField m)ˣ) :
    d.twist (torus a b) =
      torus (Units.map (titsEnd m).toMonoidHom b) (Units.map (theta m).toMonoidHom a) := by
  rw [d.twist_eq_reeAutomorphism, reeAutomorphism_apply]
  simp only [torus, map_mul, reeTwist_torusWord, exceptionalRootPermutation_simple]
  rw [rootFieldEnd_one, rootFieldEnd_two]
  exact (coroot_commute 2 1 _ _).eq

/-- All fixed torus parameters, with no lower bound on the field degree. -/
theorem torus_fixed_iff (d : LocalBlockInput m) (a b : (CoefficientField m)ˣ) :
    d.twist (torus a b) = torus a b ↔ a = Units.map (titsEnd m).toMonoidHom b := by
  rw [twist_torus]
  constructor
  · intro h
    exact (torus_injective h).1.symm
  · rintro rfl
    congr 1
    apply Units.ext
    exact theta_tits _

theorem torusFactor_fixed (d : LocalBlockInput m) (b : (CoefficientField m)ˣ) :
    d.twist (torusFactor b) = torusFactor b :=
  (torus_fixed_iff d _ _).mpr rfl

end ReeF4.LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration.SuzukiNormalizer
