module

public import Theory.SpecificGroups.ReeF4.EvenInvolutionGeometry.Roots
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.BinaryRootNormalization.Layout
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.LinearCore.CommutatorGeneration.TorusAction
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.TorusScaling

/-!
# Fixed torus actors for every nonzero Ree root parameter

On the fifth block's central curve the paired end-node coroot word has
character u: its two absolute roots have end-node weights (1,0) and (0,1).
On the paired end curve the existing middle-node word has character u⁻².
The square map of the finite characteristic-two field is bijective, so
both constructions supply every required nonzero scalar.

The actors belong to the actual exceptional-twist fixed group. The long
curve conjugacy and end-curve conjugator are consumed by binary root
normalization after the explicit Weyl change of coordinates.

Source: GLS3, Table 2.4 and §2.4; the binary representatives in
Guralnick--Malle, *Classification of 2F-modules, II*, Lemma 8.8, p.57.
-/

public section
noncomputable section
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.Normalization
open ReeF4.NormalizedRootCentralizers.CenterExponent
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open Parabolics Parabolics.RadicalCoordinates.FixedCoordinates
open Parabolics.OuterLocal.SuzukiCommutators
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration.MatrixRelations
open LargeLocalSeeds.LinearCommutators

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

private theorem endTorus_root (m : ℕ) (u : (CoefficientField m)ˣ)
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

private theorem high_coordinates : (highRoot 4).val = ![1, 1, 0, 0] := by
  have h := rootBlocks_roots_val .positive (.inr ((1 : Fin 4), (3 : Fin 4)))
  have hh := positiveRootWordLayout.quartet_high (1 : Fin 4)
  rw [positive_layout_blocks, positive_quartet_indices] at hh
  change ((rootBlocks .positive).roots (.inr ((1 : Fin 4), (3 : Fin 4)))).val = highRoot 4 at hh
  rw [hh] at h
  exact h

private theorem mixed_coordinates : (mixedRoot 4).val = ![1, 0, 0, 0] := by
  have h := rootBlocks_roots_val .positive (.inr ((1 : Fin 4), (2 : Fin 4)))
  have hh := positiveRootWordLayout.quartet_mixed (1 : Fin 4)
  rw [positive_layout_blocks, positive_quartet_indices] at hh
  change ((rootBlocks .positive).roots (.inr ((1 : Fin 4), (2 : Fin 4)))).val = mixedRoot 4 at hh
  rw [hh] at h
  exact h

private theorem high_pairing (j : Fin 4) :
    typeF4RootPairing.pairingIn ℤ (highRoot 4) (typeF4SimpleRootIndex j) =
      if j = 0 then 1 else 0 := by
  apply (FaithfulSMul.algebraMap_injective ℤ ℝ)
  rw [RootPairing.algebraMap_pairingIn, typeF4RootPairing_pairing,
    typeF4CorootScale_simpleRoot, high_coordinates, typeF4SimpleRootIndex_val]
  fin_cases j <;> norm_num [typeF4SimpleRoot, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, Fin.ext_iff]

private theorem mixed_pairing (j : Fin 4) :
    typeF4RootPairing.pairingIn ℤ (mixedRoot 4) (typeF4SimpleRootIndex j) =
      if j = 3 then 1 else 0 := by
  apply (FaithfulSMul.algebraMap_injective ℤ ℝ)
  rw [RootPairing.algebraMap_pairingIn, typeF4RootPairing_pairing,
    typeF4CorootScale_simpleRoot, mixed_coordinates, typeF4SimpleRootIndex_val]
  fin_cases j <;> norm_num [typeF4SimpleRoot, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, Fin.ext_iff]

theorem endTorus_central_scaling (m : ℕ) (u : (CoefficientField m)ˣ)
    (t : CoefficientField m) :
    endTorusWord m u * centralWord m 4 t * (endTorusWord m u)⁻¹ =
      centralWord m 4 ((u : CoefficientField m) * t) := by
  have hf : rootFieldEnd m (typeF4SimpleRootIndex 0) = rootFieldEnd m (longRoot 4) := by
    have h0 : IsLongRoot (typeF4SimpleRootIndex 0) :=
      (typeF4SimpleRootIndex_mem_pair_iff 0).mpr (by decide)
    simp only [rootFieldEnd, if_pos h0, if_pos (longRoot_isLong 4)]
  calc
    _ = (endTorusWord m u * rootGeneratorInGroup m (highRoot 4) t * (endTorusWord m u)⁻¹) *
        (endTorusWord m u * rootGeneratorInGroup m (mixedRoot 4)
          (rootFieldEnd m (longRoot 4) t) * (endTorusWord m u)⁻¹) := by
      simp [centralWord, mul_assoc]
    _ = _ := by
      rw [endTorus_root, endTorus_root, high_pairing, high_pairing,
        mixed_pairing, mixed_pairing]
      simp [centralWord, hf, map_mul]

theorem long_parameter_conjugate (m : ℕ) (a : CoefficientField m) (ha : a ≠ 0) :
    IsConj (EvenInvolutionGeometry.longRootElement m 1)
      (EvenInvolutionGeometry.longRootElement m a) := by
  let u := Units.mk0 a ha
  let h : Model m := ⟨endTorusWord m u, by
    simpa only [mem_fixedSubgroup, LocalBlockInput.twist_eq_reeAutomorphism,
      reeAutomorphism_apply] using endTorusWord_fixed (canonicalLocalBlockInput m) u⟩
  refine isConj_iff.mpr ⟨h, ?_⟩
  apply toSplitGroup_injective m
  simp only [map_mul, map_inv]
  rw [EvenInvolutionGeometry.longRootElement_coe, EvenInvolutionGeometry.longRootElement_coe]
  simp only [toSplitGroup_apply]
  change endTorusWord m u * centralWord m 4 1 * (endTorusWord m u)⁻¹ = centralWord m 4 a
  simpa only [u, Units.val_mk0, mul_one] using endTorus_central_scaling m u 1

theorem end_parameter_conjugator (m : ℕ) (a : CoefficientField m) (ha : a ≠ 0) :
    ∃ h : Model m, toSplitGroup m h * endRootWord m 1 * (toSplitGroup m h)⁻¹ =
      endRootWord m a := by
  obtain ⟨v, hv⟩ := Finite.surjective_of_injective
    (f := fun v : CoefficientField m => v ^ 2) (frobenius_inj (CoefficientField m) 2) a⁻¹
  change v ^ 2 = a⁻¹ at hv
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide)] at hv
    exact (inv_ne_zero ha) hv.symm
  let u := Units.mk0 v hv0
  let h : Model m := ⟨middleTorusWord m u, by
    simpa only [mem_fixedSubgroup, LocalBlockInput.twist_eq_reeAutomorphism,
      reeAutomorphism_apply] using middleTorusWord_fixed (canonicalLocalBlockInput m) u⟩
  refine ⟨h, ?_⟩
  have hs := congrArg (fun x => x.val.val)
    (middleTorusElement_scaling (canonicalLocalBlockInput m) u 1)
  change middleTorusWord m u * endRootWord m 1 * (middleTorusWord m u)⁻¹ =
    endRootWord m (((u : CoefficientField m) ^ 2)⁻¹ * 1) at hs
  simp only [toSplitGroup_apply]
  change middleTorusWord m u * endRootWord m 1 * (middleTorusWord m u)⁻¹ = endRootWord m a
  simpa only [u, Units.val_mk0, hv, inv_inv, mul_one] using hs

end ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.Normalization
