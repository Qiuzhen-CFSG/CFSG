module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.SeedGeneration.SuzukiLeviGeneration.FixedNormalizer.Torus

/-!
# Middle Weyl lifts act on the full two-coroot torus

The nonzero entries of an integral simple Tits lift respect the reflected
Chevalley weights. Comparing diagonal entries therefore gives its exact
commutation rule with a simple-coroot word. For the middle B₂ subsystem,
the two rules are `(a,b) ↦ (a⁻¹b²,b)` and `(a,b) ↦ (a,b⁻¹a)`.
They retain precisely the two middle parameters, with no outer coroot added.

The weight calculation adapts the private simple-diagonal calculation in
`ParabolicAmalgam/Geometry/CorootRealization.lean`; its public coroot-word
realization identifies these matrices with the literal group elements.
Source: GLS3, 1.12.1 and 2.4.8, `refs/KGroup/GLS3/Chapter1.tex`
and `refs/KGroup/GLS3/chapter2.tex`.
-/

public section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
namespace ReeF4.LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration.SuzukiNormalizer
open Parabolics Binary.FixedGeometry
noncomputable section
variable {m : ℕ}

private abbrev diag (m : ℕ) (i : typeF4RootPairing_base.support) (u : (CoefficientField m)ˣ) :=
  integralChevalleyTorusElement (P := typeF4RootPairing)
    (integralChevalleySimpleCorootParameter i u)

private theorem basisUnit_simple (m : ℕ) (q : typeF4RootPairing_base.support)
    (u : (CoefficientField m)ˣ) (a : F4Chevalley.BasisIndex) :
    chevalleyBasisTorusUnit (P := typeF4RootPairing)
      (integralChevalleySimpleCorootParameter q u) a =
      u ^ (-chevalleyBasisWeight (P := typeF4RootPairing) a q) := by
  unfold chevalleyBasisTorusUnit integralChevalleySimpleCorootParameter
  rw [Finset.prod_eq_single q]
  · simp
  · intro j _ hj; simp [hj]
  · simp

private theorem weight_reflection (a : F4Chevalley.BasisIndex)
    (i q : F4Chevalley.Root) :
    chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4RootPairing.reflectionPerm i q) =
      chevalleyBasisWeight (P := typeF4RootPairing) a q -
        typeF4RootPairing.pairingIn ℤ i q * chevalleyBasisWeight (P := typeF4RootPairing) a i := by
  cases a with
  | inl j => simp [chevalleyBasisWeight]
  | inr r =>
    simp only [chevalleyBasisWeight, typeF4RootPairing.pairingIn_reflectionPerm]
    have hr : typeF4RootPairing.root (typeF4RootPairing.reflectionPerm i r) =
        (1 : ℤ) • typeF4RootPairing.root r +
          (-typeF4RootPairing.pairingIn ℤ r i) • typeF4RootPairing.root i := by
      rw [typeF4RootPairing.root_reflectionPerm, typeF4RootPairing.reflection_apply_root]
      simp [sub_eq_add_neg, ← typeF4RootPairing.algebraMap_pairingIn ℤ,
        Int.cast_smul_eq_zsmul]
    simpa [smul_eq_mul, sub_eq_add_neg, mul_comm] using
      (typeF4RootPairing.pairingIn_eq_add_of_root_eq_smul_add_smul (S := ℤ) (j := q) hr)

private theorem tits_simple_diag (m : ℕ) (i q : typeF4RootPairing_base.support)
    (u : (CoefficientField m)ˣ) :
    rootCurveTitsWord [i] * diag m q u =
      (diag m q u * diag m i (u ^ (-typeF4RootPairing.pairingIn ℤ i q))) *
        rootCurveTitsWord [i] := by
  apply Units.ext
  change specializeMatrix (titsWord [i]) * Matrix.diagonal _ =
    (Matrix.diagonal _ * Matrix.diagonal _) * specializeMatrix (titsWord [i])
  simp only [titsWord, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
  ext row col
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hz : titsLift i row col = 0
  · simp [specializeMatrix, hz]
  · have hw := titsLift_respectsChevalleyGrading i row col hz
      (typeF4RootPairing.reflectionPerm i q)
    rw [typeF4RootPairing.reflectionPerm_self, weight_reflection] at hw
    have hu : chevalleyBasisTorusUnit (P := typeF4RootPairing)
        (integralChevalleySimpleCorootParameter q u) col =
        chevalleyBasisTorusUnit (P := typeF4RootPairing)
          (integralChevalleySimpleCorootParameter q u) row *
        chevalleyBasisTorusUnit (P := typeF4RootPairing)
          (integralChevalleySimpleCorootParameter i
            (u ^ (-typeF4RootPairing.pairingIn ℤ i q))) row := by
      rw [basisUnit_simple, basisUnit_simple, basisUnit_simple, ← zpow_mul, ← zpow_add]
      congr 1
      rw [← hw]
      ring
    rw [hu, Units.val_mul]
    exact mul_comm _ _


theorem simple_coroot_commutation (i j : Fin 4) (t : (CoefficientField m)ˣ) :
    simpleWord m [i] * torusWord m (typeF4SimpleRootIndex j) t =
      (torusWord m (typeF4SimpleRootIndex j) t *
        torusWord m (typeF4SimpleRootIndex i) (t ^ (-typeF4CartanMatrix i j))) *
          simpleWord m [i] := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, simpleWord_coe, List.map_cons, List.map_nil,
    ← typeF4RootPairing_baseEquiv_val i, ← typeF4RootPairing_baseEquiv_val j,
    torusWord_simple_coe]
  have hp : typeF4RootPairing.pairingIn ℤ (typeF4RootPairing_baseEquiv i)
      (typeF4RootPairing_baseEquiv j) = typeF4CartanMatrix i j :=
    typeF4RootPairing_base_cartan_apply i j
  have h := tits_simple_diag m (typeF4RootPairing_baseEquiv i) (typeF4RootPairing_baseEquiv j) t⁻¹
  simp only [hp, inv_zpow] at h
  apply Units.ext
  exact congrArg Units.val h

private theorem coroot_mul (i : Fin 4) (a b : (CoefficientField m)ˣ) :
    torusWord m (typeF4SimpleRootIndex i) a * torusWord m (typeF4SimpleRootIndex i) b =
      torusWord m (typeF4SimpleRootIndex i) (a*b) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, ← typeF4RootPairing_baseEquiv_val i, torusWord_simple_coe,
    ← map_mul]
  congr 1
  funext j
  simp only [integralChevalleySimpleCorootParameter, Pi.mul_apply]
  split_ifs <;> simp [mul_comm]

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

theorem simple_one_torus (a b : (CoefficientField m)ˣ) :
    simpleWord m [1] * torus a b = torus (a⁻¹ * b^2) b * simpleWord m [1] := by
  have h11 := simple_coroot_commutation (m := m) 1 1 a
  have h12 := simple_coroot_commutation (m := m) 1 2 b
  norm_num [typeF4CartanMatrix, Fin.ext_iff] at h11 h12
  dsimp only [torus]
  rw [← mul_assoc, h11, mul_assoc _ (simpleWord m [1]), h12]
  rw [← mul_assoc, ← mul_assoc, coroot_mul]
  rw [mul_assoc (torusWord m _ (a * (a^2)⁻¹)) (torusWord m _ b) (torusWord m _ (b^2)),
    (coroot_commute 2 1 b (b^2)).eq, ← mul_assoc, coroot_mul]
  rw [show a * (a^2)⁻¹ * b^2 = a⁻¹ * b^2 by group]

theorem simple_two_torus (a b : (CoefficientField m)ˣ) :
    simpleWord m [2] * torus a b = torus a (b⁻¹ * a) * simpleWord m [2] := by
  have h21 := simple_coroot_commutation (m := m) 2 1 a
  have h22 := simple_coroot_commutation (m := m) 2 2 b
  norm_num [typeF4CartanMatrix, Fin.ext_iff] at h21 h22
  dsimp only [torus]
  rw [← mul_assoc, h21, mul_assoc _ (simpleWord m [2]), h22]
  rw [← mul_assoc, ← mul_assoc,
    mul_assoc (torusWord m _ a) (torusWord m _ a) (torusWord m _ b), coroot_mul,
    mul_assoc (torusWord m _ a) (torusWord m _ (a*b)) (torusWord m _ (b^2)⁻¹), coroot_mul]
  rw [show a * b * (b^2)⁻¹ = b⁻¹ * a by simp [pow_two, mul_inv_rev, mul_comm]]

end
end ReeF4.LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration.SuzukiNormalizer
