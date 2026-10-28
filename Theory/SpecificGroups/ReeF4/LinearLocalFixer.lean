module

public import Theory.SpecificGroups.ReeF4.NormalizedRootCentralizers.Torus
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.LinearCore.CommutatorGeneration.TorusAction
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry
public import Theory.SpecificGroups.ReeF4.AutomorphismTwoRank
public import Theory.SpecificGroups.ReeF4.EvenInvolutionGeometry.UnipotentCenter
public import Theory.GroupAction.InnerInvolutionGeometry

/-!
# Involutions fixing the linear Ree parabolic residual

An involutory automorphism is inner. If it fixes the actual linear local
factor pointwise, its inner representative centralizes the full unipotent
Sylow subgroup and lies in its center, the long-root curve. The fixed
end-node torus belongs to the linear residual and scales that curve
faithfully, so the representative is trivial.

The torus calculation uses the same root and coroot conventions as
`EvenInvolutionGeometry.RadicalIntersection` and
`LargeLocalSeeds.LinearCore.CommutatorGeneration.TorusAction`.
No abstract carrier label or automorphism-fixer premise is assumed.
The point-control consumer is Chapter10.PointControl.Quasisimple.RankTwo.Ree.
Source: Aschbacher–Smith, F.1.12, printed pp.263–264, and the common-centralizer
comparison in 10.2.9, printed pp.750–751.
-/

public section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction Subgroup
namespace ReeF4.LinearLocalFixer
open Parabolics LargeLocalSeeds EvenInvolutionGeometry LinearCommutators
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open MatrixRelations
noncomputable section
private def reflectedVector : Fin 4 → Vec 4 → Vec 4
  | 0, v => ![v 0, v 2, v 1, v 3]
  | 1, v => ![v 0, v 1, v 3, v 2]
  | 2, v => ![v 0, v 1, v 2, -v 3]
  | 3, v => ![(v 0 + v 1 + v 2 + v 3) / 2,
      (v 0 + v 1 - v 2 - v 3) / 2,
      (v 0 - v 1 + v 2 - v 3) / 2,
      (v 0 - v 1 - v 2 + v 3) / 2]
private theorem reflection_val (i : Fin 4) (r : F4Chevalley.Root) :
    (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r).val =
      reflectedVector i r.val := by
  change typeF4RootPairing.root (typeF4RootPairing.reflectionPerm _ r) = _
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root,
    typeF4RootPairing_pairing, typeF4CorootScale_simpleRoot]
  simp only [typeF4RootPairing_root, typeF4SimpleRootIndex_val]
  fin_cases i <;> ext k <;> fin_cases k <;>
    simp [reflectedVector, typeF4SimpleRoot, dot, Fin.sum_univ_four] <;> ring

private theorem long_four_val : (longRoot 4).val = ![1,-1,0,0] := by
  rw [longRoot_eq_sum]
  ext k; fin_cases k <;>
    norm_num [longRootCoefficients, typeF4SimpleRoot, Fin.sum_univ_four,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]

private theorem short_four_val : (shortRoot 4).val = ![0,1,0,0] := by
  ext k; fin_cases k <;>
    norm_num [shortRoot, longRoot, relativeRotation, middleReflection, endReflection,
      Equiv.Perm.mul_apply, pow_succ,
      WordRelations.exceptionalRootPermutation_simple_reflection,
      exceptionalRootPermutation_simple, Fin.revPerm, Fin.rev,
      reflection_val, reflectedVector, typeF4SimpleRoot,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]

private theorem high_four_val : (highRoot 4).val = ![1,1,0,0] := by
  rw [highRoot_eq_add_two 4 (by decide), long_four_val, short_four_val]
  ext k; fin_cases k <;> norm_num

private theorem mixed_four_val : (mixedRoot 4).val = ![1,0,0,0] := by
  rw [mixedRoot_eq_add 4 (by decide), long_four_val, short_four_val]
  ext k; fin_cases k <;> norm_num

private theorem high_pairing (j : Fin 4) :
    typeF4RootPairing.pairingIn ℤ (highRoot 4) (typeF4SimpleRootIndex j) =
      if j = 0 then 1 else 0 := by
  apply Int.cast_injective (α := ℝ)
  rw [show (↑(typeF4RootPairing.pairingIn ℤ (highRoot 4)
    (typeF4SimpleRootIndex j)) : ℝ) =
      typeF4RootPairing.pairing (highRoot 4) (typeF4SimpleRootIndex j) from
        typeF4RootPairing.algebraMap_pairingIn ℤ _ _]
  rw [typeF4RootPairing_pairing, typeF4CorootScale_simpleRoot, high_four_val,
    typeF4SimpleRootIndex_val]
  fin_cases j <;> norm_num [typeF4SimpleRoot, dot, Fin.sum_univ_four, Matrix.cons_val_two,
    Matrix.cons_val_three, Fin.ext_iff]

private theorem mixed_pairing (j : Fin 4) :
    typeF4RootPairing.pairingIn ℤ (mixedRoot 4) (typeF4SimpleRootIndex j) =
      if j = 3 then 1 else 0 := by
  apply Int.cast_injective (α := ℝ)
  rw [show (↑(typeF4RootPairing.pairingIn ℤ (mixedRoot 4)
    (typeF4SimpleRootIndex j)) : ℝ) =
      typeF4RootPairing.pairing (mixedRoot 4) (typeF4SimpleRootIndex j) from
        typeF4RootPairing.algebraMap_pairingIn ℤ _ _]
  rw [typeF4RootPairing_pairing, typeF4CorootScale_simpleRoot, mixed_four_val,
    typeF4SimpleRootIndex_val]
  fin_cases j <;> norm_num [typeF4SimpleRoot, dot, Fin.sum_univ_four, Matrix.cons_val_two,
    Matrix.cons_val_three, Fin.ext_iff]

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


/-- The fixed end-node torus scales the actual long-root curve. -/
theorem endTorus_longRoot (m : ℕ) (u : (CoefficientField m)ˣ) (t : CoefficientField m) :
    endTorusWord m u * centralWord m 4 t * (endTorusWord m u)⁻¹ =
      centralWord m 4 (u * t) := by
  have hf : rootFieldEnd m (typeF4SimpleRootIndex 0) = rootFieldEnd m (longRoot 4) := by
    have h0 : IsLongRoot (typeF4SimpleRootIndex 0) :=
      (typeF4SimpleRootIndex_mem_pair_iff 0).mpr (by decide)
    simp [rootFieldEnd, h0, longRoot_isLong]
  calc
    _ = (endTorusWord m u * rootGeneratorInGroup m (highRoot 4) t *
          (endTorusWord m u)⁻¹) *
        (endTorusWord m u * rootGeneratorInGroup m (mixedRoot 4)
          (rootFieldEnd m (longRoot 4) t) * (endTorusWord m u)⁻¹) := by
      simp only [centralWord]; group
    _ = _ := by
      rw [endTorusWord_root, endTorusWord_root]
      simp [high_pairing, mixed_pairing, centralWord, hf]

/-- No nonidentity point of the long-root curve centralizes the linear local factor. -/
theorem longRoot_eq_one_of_centralizes {m : ℕ} (hm : 1 ≤ m)
    (t : CoefficientField m)
    (hc : longRootElement m t ∈ centralizer (localFactor m .linear : Set (Model m))) :
    longRootElement m t = 1 := by
  have hq : 2 < Nat.card (CoefficientField m) := by
    rw [field_card]
    exact lt_of_lt_of_le (by decide : 2 < 2 ^ 3)
      (Nat.pow_le_pow_right (by decide) (by omega))
  let : Nontrivial (CoefficientField m)ˣ := by
    apply Finite.one_lt_card_iff_nontrivial.mp
    rw [Nat.card_units]
    omega
  obtain ⟨u, hu⟩ := exists_ne (1 : (CoefficientField m)ˣ)
  let z := seedEquiv m .linear (endTorusElement (canonicalLocalBlockInput m) u)
  have hz : (z : Model m) ∈ localFactor m .linear := seed_eq_localFactor m .linear ▸ z.property
  have hc' := hc _ hz
  have hword : Commute (endTorusWord m u) (centralWord m 4 t) := by
    change _ * _ = _ * _
    have he := congrArg (toSplitGroup m) hc'
    simpa only [map_mul, z, seedEquiv_coe, longRootElement_coe, endTorusElement] using he
  have hscale : centralWord m 4 (u * t) = centralWord m 4 t := by
    rw [← endTorus_longRoot, hword.eq, mul_inv_cancel_right]
  have hparam : (u : CoefficientField m) * t = t :=
    longRootElement_injective m (Subtype.ext hscale)
  have ht : t = 0 := by
    by_contra hn
    apply hu
    apply Units.ext
    exact mul_right_cancel₀ hn (hparam.trans (one_mul t).symm)
  simp [ht]

/-- Involutions fixing the literal linear parabolic residual pointwise are trivial. -/
theorem eq_one_of_fixes_linearLocal {m : ℕ} (hm : 1 ≤ m)
    [IsSimpleGroup (Model m)] [Group.IsPerfect (Model m)]
    (a : MulAut (Model m)) (ha : a ^ 2 = 1)
    (hf : ∀ x ∈ localFactor m .linear, a x = x) : a = 1 := by
  obtain ⟨x, hx⟩ := Parabolics.OuterLocal.LargeAutomorphisms.inner_of_sq_eq_one hm a ha
  have hx2 : x ^ 2 = 1 := by
    apply MulAut.conj_injective_of_center_eq_bot center_eq_bot_of_simple_perfect
    rw [map_pow, hx, ha, map_one]
  let S := sylowOfOddIndex m (AutomorphismTwoRank.unipotent_index_odd m)
  have hS : (S : Subgroup (Model m)) = unipotent m := sylowOfOddIndex_coe m _
  obtain ⟨hxu, hxc⟩ := MulAut.involution_mem_sylow_of_centralizes S x hx2
    (fun y hy => hx ▸ hf y (unipotent_le_localFactor m .linear (hS ▸ hy)))
  change x ∈ (S : Subgroup (Model m)) at hxu
  change ∀ y ∈ (S : Subgroup (Model m)), Commute x y at hxc
  rw [hS] at hxu hxc
  have hxZ : x ∈ (center (unipotent m)).map (unipotent m).subtype := by
    exact ⟨⟨x, hxu⟩, mem_center_iff.mpr (fun y => Subtype.ext (hxc y y.property).eq.symm), rfl⟩
  rw [unipotent_center_eq_longRootGroup m hm] at hxZ
  obtain ⟨t, rfl⟩ := (mem_longRootGroup m x).mp hxZ
  have hc : longRootElement m t ∈ centralizer (localFactor m .linear : Set (Model m)) := by
    intro y hy
    have hh : (MulAut.conj (longRootElement m t)) y = y := by rw [hx]; exact hf y hy
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  rw [longRoot_eq_one_of_centralizes hm t hc, map_one] at hx
  exact hx.symm

end
end ReeF4.LinearLocalFixer
