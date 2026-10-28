module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.CorootRealization
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.RootWords
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.MatrixRelations.WeylGeometry

/-!
# The end-node torus on the middle Ree root curve

Pair the end-node coroot words using the exceptional field map. They commute,
so their product is fixed by every supplied local twist. The diagonal coroot
realization gives the inverse-unit scalar on the first main B₂ curve,
including its mixed-root correction factor. This is a concrete actor inside
the linear seed, with no complementary parabolic torus adjoined.

Source: the F₄ coroot action and exceptional twist underlying
Aschbacher–Smith F.1.12(II), printed pp.263–264.
-/

@[expose] public section
noncomputable section
namespace ReeF4.LargeLocalSeeds.LinearCommutators
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction Parabolics
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration

private theorem coroot_coe (m : ℕ) (i : Fin 4) (u : (CoefficientField m)ˣ) :
    (torusWord m (typeF4SimpleRootIndex i) u).val =
      (integralChevalleyTorusElement (P := typeF4RootPairing)
        (integralChevalleySimpleCorootParameter (typeF4RootPairing_baseEquiv i) u))⁻¹ := by
  rw [← typeF4RootPairing_baseEquiv_val, torusWord_simple_coe]
  change integralChevalleyTorusElement _ = _
  rw [← integralChevalleyTorusElement_inv]
  congr 1
  funext j
  simp only [integralChevalleySimpleCorootParameter, Pi.inv_apply]
  split_ifs <;> simp

private theorem coroot_root (m : ℕ) (i : Fin 4) (u : (CoefficientField m)ˣ)
    (r : F4Chevalley.Root) (t : CoefficientField m) :
    torusWord m (typeF4SimpleRootIndex i) u * rootGeneratorInGroup m r t *
        (torusWord m (typeF4SimpleRootIndex i) u)⁻¹ =
      rootGeneratorInGroup m r
        (((u ^ typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex i) :
          (CoefficientField m)ˣ) : CoefficientField m) * t) := by
  apply Subtype.ext
  change (torusWord m _ u).val * F4Chevalley.rootCurve _ _ *
    ((torusWord m _ u).val)⁻¹ = _
  rw [coroot_coe, inv_inv]
  exact integralChevalleyRootCurve_simpleCoroot_conjugation
    (typeF4RootPairing_baseEquiv i) u r t

private theorem coroot_commute (m : ℕ) (i j : Fin 4) (u v : (CoefficientField m)ˣ) :
    Commute (torusWord m (typeF4SimpleRootIndex i) u)
      (torusWord m (typeF4SimpleRootIndex j) v) := by
  apply Subtype.ext
  change (torusWord m _ u).val * (torusWord m _ v).val =
    (torusWord m _ v).val * (torusWord m _ u).val
  rw [coroot_coe, coroot_coe]
  apply Commute.inv_inv
  change integralChevalleyTorusElement _ * integralChevalleyTorusElement _ =
    integralChevalleyTorusElement _ * integralChevalleyTorusElement _
  simp only [← integralChevalleyTorusElement_mul, mul_comm]

/-- The torus of the end-node A₁ × A₁ Levi, with paired field parameters. -/
def endTorusWord (m : ℕ) (u : (CoefficientField m)ˣ) : SplitGroup m :=
  torusWord m (typeF4SimpleRootIndex 0) u *
    torusWord m (typeF4SimpleRootIndex 3)
      (Units.map (rootFieldEnd m (typeF4SimpleRootIndex 0) : CoefficientField m →* CoefficientField m) u)

private theorem weyl_mem (m : ℕ) (i : Fin 4) (hi : i ∈ leviNodes .linear)
    (t : CoefficientField m) :
    weylWord m (typeF4SimpleRootIndex i) t ∈ splitSeed m .linear := by
  let : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg
  have hp (a : CoefficientField m) :
      rootGeneratorInGroup m (typeF4SimpleRootIndex i) a ∈ splitSeed m .linear :=
    Subgroup.subset_closure ⟨_, _, Or.inl
      (typeF4RootPairing_base.isPos_of_mem_support (typeF4RootPairing_baseEquiv i).property), rfl⟩
  have hn (a : CoefficientField m) :
      rootGeneratorInGroup m (-typeF4SimpleRootIndex i) a ∈ splitSeed m .linear :=
    Subgroup.subset_closure ⟨_, _, Or.inr ⟨i, hi, rfl⟩, rfl⟩
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hp _) (hn _)) (hp _)

theorem endTorusWord_mem_seed (m : ℕ) (u : (CoefficientField m)ˣ) :
    endTorusWord m u ∈ splitSeed m .linear := by
  have ht (i : Fin 4) (hi : i ∈ leviNodes .linear) (v : (CoefficientField m)ˣ) :
      torusWord m (typeF4SimpleRootIndex i) v ∈ splitSeed m .linear :=
    Subgroup.mul_mem _ (weyl_mem m i hi _) (weyl_mem m i hi _)
  exact Subgroup.mul_mem _ (ht 0 (by simp [leviNodes]) _) (ht 3 (by simp [leviNodes]) _)

theorem endTorusWord_fixed {m : ℕ} (d : LocalBlockInput m) (u : (CoefficientField m)ˣ) :
    d.twist (endTorusWord m u) = endTorusWord m u := by
  have h0 : exceptionalRootPermutation (typeF4SimpleRootIndex 0) =
      typeF4SimpleRootIndex 3 := exceptionalRootPermutation_simple 0
  have h3 : exceptionalRootPermutation (typeF4SimpleRootIndex 3) =
      typeF4SimpleRootIndex 0 := exceptionalRootPermutation_simple 3
  have htwice : Units.map (rootFieldEnd m (typeF4SimpleRootIndex 3) : CoefficientField m →* CoefficientField m)
      (Units.map (rootFieldEnd m (typeF4SimpleRootIndex 0) : CoefficientField m →* CoefficientField m) u) = u := by
    apply Units.ext
    exact h0 ▸ RadicalCoordinates.rootFieldEnd_twice m (typeF4SimpleRootIndex 0) u.val
  rw [d.twist_eq_reeAutomorphism, reeAutomorphism_apply]
  simp only [endTorusWord, map_mul, reeTwist_torusWord, h0, h3]
  rw [htwice]
  exact (coroot_commute m 0 3 u (Units.map (rootFieldEnd m (typeF4SimpleRootIndex 0) : CoefficientField m →* CoefficientField m) u)).eq.symm

/-- A concrete fixed torus actor inside the linear seed. -/
def endTorusElement {m : ℕ} (d : LocalBlockInput m) (u : (CoefficientField m)ˣ) :
    standardSeed d .linear :=
  ⟨⟨endTorusWord m u, endTorusWord_fixed d u⟩, endTorusWord_mem_seed m u⟩

private theorem endTorusWord_root (m : ℕ) (u : (CoefficientField m)ˣ)
    (r : F4Chevalley.Root) (t : CoefficientField m) :
    endTorusWord m u * rootGeneratorInGroup m r t * (endTorusWord m u)⁻¹ =
      rootGeneratorInGroup m r
        (((u ^ typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 0) :
          (CoefficientField m)ˣ) : CoefficientField m) *
        (((Units.map (rootFieldEnd m (typeF4SimpleRootIndex 0) : CoefficientField m →* CoefficientField m) u ^
            typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 3) :
          (CoefficientField m)ˣ) : CoefficientField m) * t)) := by
  unfold endTorusWord
  rw [mul_inv_rev]
  calc
    _ = torusWord m (typeF4SimpleRootIndex 0) u *
      (torusWord m (typeF4SimpleRootIndex 3) (Units.map (rootFieldEnd m (typeF4SimpleRootIndex 0) : CoefficientField m →* CoefficientField m) u) *
        rootGeneratorInGroup m r t *
        (torusWord m (typeF4SimpleRootIndex 3) (Units.map (rootFieldEnd m (typeF4SimpleRootIndex 0) : CoefficientField m →* CoefficientField m) u))⁻¹) *
      (torusWord m (typeF4SimpleRootIndex 0) u)⁻¹ := by group
    _ = _ := by rw [coroot_root, coroot_root]

private theorem simple_pairing (i j : Fin 4) :
    typeF4RootPairing.pairingIn ℤ (typeF4SimpleRootIndex i) (typeF4SimpleRootIndex j) =
      typeF4CartanMatrix i j := typeF4RootPairing_base_cartan_apply i j

private theorem mixed_pairing (j : Fin 4) :
    typeF4RootPairing.pairingIn ℤ (mixedRoot 0) (typeF4SimpleRootIndex j) =
      typeF4CartanMatrix 1 j + typeF4CartanMatrix 2 j := by
  have h := typeF4RootPairing.pairingIn_eq_add_of_root_eq_smul_add_smul (S := ℤ)
    (i := longRoot 0) (l := shortRoot 0) (k := mixedRoot 0) (j := typeF4SimpleRootIndex j)
    (x := 1) (y := 1)
    (by simpa using MatrixRelations.mixedRoot_eq_add 0 (by decide))
  have hs : shortRoot 0 = typeF4SimpleRootIndex 2 := by
    simp [shortRoot, longRoot, exceptionalRootPermutation_simple, Fin.revPerm, Fin.rev]
  simpa only [one_smul, show longRoot 0 = typeF4SimpleRootIndex 1 from rfl, hs,
    simple_pairing] using h


/-- The mixed-root correction has the product character, so the whole B₂ main
curve is scaled by the inverse end-node parameter. -/
theorem endTorusWord_scaling (m : ℕ) (u : (CoefficientField m)ˣ) (t : CoefficientField m) :
    endTorusWord m u * rootWord m 0 t * (endTorusWord m u)⁻¹ =
      rootWord m 0 ((u : CoefficientField m)⁻¹ * t) := by
  have hf : rootFieldEnd m (typeF4SimpleRootIndex 0) =
      rootFieldEnd m (longRoot 0) := by
    have h0 : IsLongRoot (typeF4SimpleRootIndex 0) :=
      (typeF4SimpleRootIndex_mem_pair_iff 0).mpr (by decide)
    simp [rootFieldEnd, h0, MatrixRelations.longRoot_isLong]
  have hp (i j) : typeF4RootPairing.pairingIn ℤ (typeF4SimpleRootIndex i)
      (typeF4SimpleRootIndex j) = typeF4CartanMatrix i j :=
    typeF4RootPairing_base_cartan_apply i j
  simp only [rootWord, show (0 : Fin 8).val % 2 = 0 from rfl, if_true]
  calc
    _ = (endTorusWord m u * rootGeneratorInGroup m (longRoot 0) t * (endTorusWord m u)⁻¹) *
        (endTorusWord m u * rootGeneratorInGroup m (shortRoot 0)
          (rootFieldEnd m (longRoot 0) t) * (endTorusWord m u)⁻¹) *
        (endTorusWord m u * rootGeneratorInGroup m (mixedRoot 0)
          (t * rootFieldEnd m (longRoot 0) t) * (endTorusWord m u)⁻¹) := by group
    _ = _ := by
      rw [endTorusWord_root, endTorusWord_root, endTorusWord_root, mixed_pairing, mixed_pairing]
      simp only [longRoot, shortRoot, Matrix.cons_val_zero, exceptionalRootPermutation_simple,
        Fin.revPerm, hp]
      norm_num [typeF4CartanMatrix, Fin.ext_iff, hf, map_mul, map_inv₀, mul_assoc,
        mul_left_comm, mul_comm]
      rfl

end ReeF4.LargeLocalSeeds.LinearCommutators
