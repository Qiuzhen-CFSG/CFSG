module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.Parameters
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.Basic
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Transport.WeylDuality

/-!
# Characters of the recovered Ree torus

The simple-root characters `b, c, θ(c), θ(b)`, where `θ(t) = t^(2^m)`,
determine the diagonal torus `blockTorus b c`. Its characters satisfy the
exceptional twist identity on every F₄ root. To prove this globally, reindex
the product defining a root character by exceptional diagram reversal, use
that this reversal transposes the root-coroot pairing, and use the coroot
factors 1 on long roots and 2 on short roots. The finite-field identity
`θ(θ(t))^2 = t` supplies the reversed parameter identities.

The integral torus conjugation formula then scales the literal type VI and
type V words on both signs. The type V central parameter has character
`c * θ(c)^2`; its θ-image is `c * θ(c)`, which also scales the mixed root.
Opposite roots have inverse characters.

These are the root-character calculations for GLS3, Table 2.4, 2.4.7(f),
and 2.5.1(b), in `refs/KGroup/GLS3/chapter2.tex`. Conjugation follows the
existing convention `T⁻¹ * x * T`. The result is independent of block
coverage and of realizing the diagonal matrix inside the fixed group.
-/

public noncomputable section
namespace ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open WordRelations
variable {m : ℕ}
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private theorem theta_twice_sq (t : CoefficientField m) : (theta m (theta m t)) ^ 2 = t := by
  simp only [theta_apply, ← pow_mul, ← pow_add]
  rw [show 2 ^ (m + m) * 2 = 2 ^ (2 * m + 1) by
    rw [pow_succ]; congr 2; omega]
  exact field_pow m t

private theorem thetaUnits_twice_sq (c : (CoefficientField m)ˣ) :
    Units.map (theta m : CoefficientField m →* CoefficientField m)
      (Units.map (theta m : CoefficientField m →* CoefficientField m) c) ^ 2 = c := by
  apply Units.ext
  exact theta_twice_sq c.val

private def rootPower (r : F4Chevalley.Root) : ℕ :=
  @ite ℕ (IsLongRoot r) (Classical.propDecidable _) 1 2

private theorem rootPower_cast (r : F4Chevalley.Root) :
    (rootPower r : ℝ) = typeF4CorootScale r := by
  classical
  by_cases hr : IsLongRoot r
  · rw [rootPower, if_pos hr, typeF4CorootScale_of_pair r hr]; norm_num
  · rw [rootPower, if_neg hr, typeF4CorootScale_of_not_pair r hr]; norm_num

private theorem pairing_symmetrized (r s : F4Chevalley.Root) :
    (rootPower r : ℤ) * typeF4RootPairing.pairingIn ℤ r s =
      (rootPower s : ℤ) * typeF4RootPairing.pairingIn ℤ s r := by
  apply Int.cast_injective (α := ℝ)
  push_cast
  rw [rootPower_cast, rootPower_cast]
  change typeF4CorootScale r * algebraMap ℤ ℝ _ =
    typeF4CorootScale s * algebraMap ℤ ℝ _
  rw [typeF4RootPairing.algebraMap_pairingIn, typeF4RootPairing.algebraMap_pairingIn,
    typeF4RootPairing_pairing, typeF4RootPairing_pairing, dot_comm s.val r.val]
  ring

private theorem blockTorus_paired (b c : (CoefficientField m)ˣ)
    (q : typeF4RootPairing_base.support) :
    blockTorus b c (simplePermutation q) =
      Units.map (theta m : CoefficientField m →* CoefficientField m)
        (blockTorus b c q) ^ rootPower q.val := by
  let f := Units.map (theta m : CoefficientField m →* CoefficientField m)
  have h0 : blockTorus b c (typeF4RootPairing_baseEquiv 3) =
      f (blockTorus b c (typeF4RootPairing_baseEquiv 0)) := by
    simp only [blockTorus, torusParametersOfSimpleScales, Equiv.symm_apply_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      map_mul, map_pow]
    change b * c ^ 2 * f c ^ 3 * f b ^ 2 =
      f b ^ 2 * f c ^ 3 * f (f c) ^ 4 * f (f b) ^ 2
    rw [show f (f c) ^ 4 = c ^ 2 by
      rw [show 4 = 2 * 2 from rfl, pow_mul, thetaUnits_twice_sq], thetaUnits_twice_sq]
    ac_rfl
  have h1 : blockTorus b c (typeF4RootPairing_baseEquiv 2) =
      f (blockTorus b c (typeF4RootPairing_baseEquiv 1)) := by
    simp only [blockTorus, torusParametersOfSimpleScales, Equiv.symm_apply_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      map_mul, map_pow]
    change b ^ 2 * c ^ 4 * f c ^ 6 * f b ^ 3 =
      f b ^ 3 * f c ^ 6 * f (f c) ^ 8 * f (f b) ^ 4
    rw [show f (f c) ^ 8 = c ^ 4 by
      rw [show 8 = 2 * 4 from rfl, pow_mul, thetaUnits_twice_sq],
      show f (f b) ^ 4 = b ^ 2 by
        rw [show 4 = 2 * 2 from rfl, pow_mul, thetaUnits_twice_sq]]
    ac_rfl
  obtain ⟨i, rfl⟩ := typeF4RootPairing_baseEquiv.surjective q
  rw [simplePermutation_numbered, typeF4RootPairing_baseEquiv_val]
  have hp (j : Fin 4) : rootPower (typeF4SimpleRootIndex j) =
      if j.val < 2 then 1 else 2 := by
    simp only [rootPower, IsLongRoot, typeF4SimpleRootIndex_mem_pair_iff]
  rw [hp]
  fin_cases i
  · exact h0.trans (pow_one _).symm
  · exact h1.trans (pow_one _).symm
  · change blockTorus b c (typeF4RootPairing_baseEquiv 1) =
      f (blockTorus b c (typeF4RootPairing_baseEquiv 2)) ^ 2
    rw [h1, thetaUnits_twice_sq]
  · change blockTorus b c (typeF4RootPairing_baseEquiv 0) =
      f (blockTorus b c (typeF4RootPairing_baseEquiv 3)) ^ 2
    rw [h0, thetaUnits_twice_sq]

private theorem rootScale_dual (b c : (CoefficientField m)ˣ) (r : F4Chevalley.Root) :
    rootScale (blockTorus b c) (exceptionalRootPermutation r) =
      Units.map (theta m : CoefficientField m →* CoefficientField m)
        (rootScale (blockTorus b c) r) ^ rootPower r := by
  simp only [rootScale, integralChevalleyRootScale]
  rw [← Equiv.prod_comp simplePermutation]
  simp only [simplePermutation_val, exceptionalRootPermutation_pairingIn, blockTorus_paired,
    map_prod, map_zpow, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro q _
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul]
  congr 1
  rw [← pairing_symmetrized]
  exact mul_comm _ _

/-- The recovered torus is compatible with the twist on every root. -/
theorem blockTorus_twistCompatible (b c : (CoefficientField m)ˣ) :
    TwistCompatible (blockTorus b c) := by
  intro r
  rw [rootScale_dual]
  change exceptionalParameter r (theta m (rootScale (blockTorus b c) r : CoefficientField m)) =
    theta m (rootScale (blockTorus b c) r : CoefficientField m) ^ rootPower r
  classical
  by_cases hr : IsLongRoot r
  · simp only [exceptionalParameter_of_long hr, rootPower, if_pos hr, pow_one]
  · simp only [exceptionalParameter_of_short hr, rootPower, if_neg hr]

private theorem pairing_reflection (i r j : F4Chevalley.Root) :
    typeF4RootPairing.pairingIn ℤ (typeF4RootPairing.reflectionPerm i r) j =
      typeF4RootPairing.pairingIn ℤ r j -
        typeF4RootPairing.pairingIn ℤ r i * typeF4RootPairing.pairingIn ℤ i j := by
  apply Int.cast_injective (α := ℝ)
  push_cast
  change algebraMap ℤ ℝ _ = algebraMap ℤ ℝ _ - algebraMap ℤ ℝ _ * algebraMap ℤ ℝ _
  simp only [typeF4RootPairing.algebraMap_pairingIn]
  simp only [RootPairing.pairing, RootPairing.root', typeF4RootPairing.root_reflectionPerm,
    typeF4RootPairing.reflection_apply_root, map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul]

private theorem rootScale_reflection (u : TorusParameters m) (i r : F4Chevalley.Root) :
    rootScale u (typeF4RootPairing.reflectionPerm i r) =
      rootScale u r * rootScale u i ^ (-typeF4RootPairing.pairingIn ℤ r i) := by
  simp only [rootScale, integralChevalleyRootScale, pairing_reflection]
  simp only [sub_eq_add_neg, zpow_add, mul_comm
    (typeF4RootPairing.pairingIn ℤ r i), ← mul_neg, zpow_mul, Finset.prod_mul_distrib,
    Finset.prod_zpow]

private theorem rootScale_neg (u : TorusParameters m) (r : F4Chevalley.Root) :
    rootScale u (-r) = (rootScale u r)⁻¹ := by
  simp only [rootScale, integralChevalleyRootScale, RootPairing.indexNeg_neg,
    RootPairing.pairingIn_reflectionPerm_self_left, zpow_neg, Finset.prod_inv_distrib]

private theorem rootScale_signedRoot (u : TorusParameters m) (positive : Bool)
    (r : F4Chevalley.Root) :
    rootScale u (signedRoot positive r) = signedScale (rootScale u r) positive := by
  cases positive <;> simp only [signedRoot, signedScale, Bool.false_eq_true,
    ↓reduceIte, rootScale_neg]

private theorem signedScale_mul (a b : (CoefficientField m)ˣ) (positive : Bool) :
    signedScale (a * b) positive = signedScale a positive * signedScale b positive := by
  cases positive <;> simp [signedScale, mul_comm]

private theorem signedScale_theta (a : (CoefficientField m)ˣ) (positive : Bool) :
    signedScale (Units.map (theta m : CoefficientField m →* CoefficientField m) a) positive =
      Units.map (theta m : CoefficientField m →* CoefficientField m) (signedScale a positive) := by
  cases positive <;> simp [signedScale]

private theorem rootScale_blockTorus_simple (b c : (CoefficientField m)ˣ) (i : Fin 4) :
    rootScale (blockTorus b c) (typeF4SimpleRootIndex i) =
      ![b, c, Units.map (theta m : CoefficientField m →* CoefficientField m) c,
        Units.map (theta m : CoefficientField m →* CoefficientField m) b] i :=
  rootScale_torusParametersOfSimpleScales _ i

private theorem rootScale_linearRoots (b c : (CoefficientField m)ˣ) (positive : Bool)
    (i : Fin 2) : rootScale (blockTorus b c) (linearRoots positive i) =
      ![signedScale b positive,
        Units.map (theta m : CoefficientField m →* CoefficientField m)
          (signedScale b positive)] i := by
  fin_cases i <;> simp [linearRoots, rootScale_signedRoot, rootScale_blockTorus_simple,
    signedScale_theta]

private theorem rootScale_suzukiRoots (b c : (CoefficientField m)ˣ) (positive : Bool)
    (i : Fin 4) : rootScale (blockTorus b c) (suzukiRoots positive i) =
      ![signedScale c positive,
        Units.map (theta m : CoefficientField m →* CoefficientField m) (signedScale c positive),
        signedScale (centralScale c) positive,
        signedScale c positive *
          Units.map (theta m : CoefficientField m →* CoefficientField m)
            (signedScale c positive)] i := by
  have hp (i j : Fin 4) : typeF4RootPairing.pairingIn ℤ (typeF4SimpleRootIndex i)
      (typeF4SimpleRootIndex j) = typeF4CartanMatrix i j :=
    typeF4RootPairing_base_cartan_apply i j
  fin_cases i <;> norm_num [suzukiRoots, rootScale_signedRoot, rootScale_reflection,
    rootScale_blockTorus_simple, hp, typeF4CartanMatrix, centralScale, Fin.ext_iff,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    signedScale_mul, signedScale_theta, mul_comm]

private theorem theta_centralScale (c : (CoefficientField m)ˣ) :
    Units.map (theta m : CoefficientField m →* CoefficientField m) (centralScale c) =
      c * Units.map (theta m : CoefficientField m →* CoefficientField m) c := by
  simp only [centralScale, map_mul, map_pow, thetaUnits_twice_sq, mul_comm]

private theorem theta_signed_centralScale (c : (CoefficientField m)ˣ) (positive : Bool) :
    theta m (signedScale (centralScale c) positive : CoefficientField m) =
      (signedScale c positive : CoefficientField m) *
        theta m (signedScale c positive : CoefficientField m) := by
  change (Units.map (theta m : CoefficientField m →* CoefficientField m)
    (signedScale (centralScale c) positive)).val = _
  rw [← signedScale_theta, theta_centralScale, signedScale_mul, signedScale_theta]
  rfl

/-- Diagonal conjugation scales both signed type VI words. -/
theorem blockTorus_linearWord (b c : (CoefficientField m)ˣ) (positive : Bool)
    (t : CoefficientField m) :
    matrixTorusConj (blockTorus b c) (linearWord m positive t).val =
      (linearWord m positive ((signedScale b positive : CoefficientField m) * t)).val := by
  simp only [linearWord_coe, map_mul, matrixTorusConj_root, rootScale_linearRoots,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rfl

/-- Diagonal conjugation scales both parameters of both signed type V words. -/
theorem blockTorus_suzukiWord (b c : (CoefficientField m)ˣ) (positive : Bool)
    (t u : CoefficientField m) :
    matrixTorusConj (blockTorus b c) (suzukiWord m positive t u).val =
      (suzukiWord m positive ((signedScale c positive : CoefficientField m) * t)
        ((signedScale (centralScale c) positive : CoefficientField m) * u)).val := by
  simp only [suzukiWord_coe, map_mul, matrixTorusConj_root, rootScale_suzukiRoots,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, Units.val_mul, Units.coe_map, MonoidHom.coe_coe,
    theta_signed_centralScale]
  congr 2
  ring

/-- Every pair of nonzero block scales gives all the required torus word laws. -/
theorem torusWordLaws (b c : (CoefficientField m)ˣ) : TorusWordLaws b c :=
  ⟨blockTorus_twistCompatible b c, blockTorus_linearWord b c, blockTorus_suzukiWord b c⟩

end ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery
end
