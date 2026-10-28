module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.Relations
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Transport.Curves
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.FixedGeometry.WeylLifts
/-!
# Weyl geometry for the named Ree root curves

The long roots of the eight relative blocks are positive roots obtained by the
middle and end Weyl words. Exceptional duality supplies their positive short
partners. On every long root the twisting field map is the source exponent θ;
its square is the Tits map, the exponent 2θ used in the commutator formulas.

The integral B₂ braid relation fixes the middle longest word under the Ree
twist. Integral Weyl transport gives its exact action on the end-root curve.
The same argument expresses the fourth curve as a Weyl conjugate of the
additive end curve, proving its additivity for every parameter m, including 0.

Source: GLS3, 2.3.8 and Table 2.4, `refs/KGroup/GLS3/chapter2.tex`.
These are the Weyl and additive inputs to the normal-generation argument
underlying Aschbacher–Smith F.1.12(II)(i), printed pp.263–264.
-/

@[expose] public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open ReeF4 ReeF4.Parabolics
namespace ReeF4.Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
noncomputable section
namespace MatrixRelations

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

def longRootCoefficients : Fin 8 → Fin 4 → ℕ :=
  ![![0,1,0,0], ![1,2,2,0], ![1,1,2,0], ![1,2,4,2],
    ![0,1,2,2], ![1,2,2,2], ![1,1,0,0], ![1,0,0,0]]

theorem longRoot_eq_sum (i : Fin 8) :
    (longRoot i).val = ∑ j : Fin 4, longRootCoefficients i j • typeF4SimpleRoot j := by
  fin_cases i <;> funext k <;> fin_cases k <;>
    simp only [Fin.sum_univ_four, Pi.add_apply, Pi.smul_apply] <;>
    norm_num [longRoot, relativeRotation, middleReflection, endReflection,
      Equiv.Perm.mul_apply, pow_succ, reflection_val, reflectedVector,
      longRootCoefficients, typeF4SimpleRoot, Matrix.cons_val_two, Matrix.cons_val_three]

theorem longRoot_pos (i : Fin 8) : typeF4RootPairing_base.IsPos (longRoot i) := by
  rw [RootPairing.Base.isPos_iff_root_mem_closure]
  change (longRoot i).val ∈ _
  rw [longRoot_eq_sum]
  apply AddSubmonoid.sum_mem
  intro j _
  apply AddSubmonoid.nsmul_mem
  apply AddSubmonoid.subset_closure
  exact ⟨typeF4SimpleRootIndex j, (typeF4RootPairing_baseEquiv j).property, rfl⟩

/-- All eight chosen first roots are geometrically long. -/
theorem longRoot_isLong (i : Fin 8) : IsLongRoot (longRoot i) := by
  fin_cases i <;>
    norm_num [longRoot, relativeRotation, middleReflection, endReflection,
      Equiv.Perm.mul_apply, pow_succ, WordRelations.isLongRoot_reflection_iff]
  all_goals
    change (typeF4SimpleRootIndex _).val ∈ pairRoots 4
    exact (typeF4SimpleRootIndex_mem_pair_iff _).mpr (by decide)

/-- The paired second roots are geometrically short. -/
theorem shortRoot_isShort (i : Fin 8) : IsShortRoot (shortRoot i) :=
  (exceptionalRootPermutation_long_iff (longRoot i)).mp (longRoot_isLong i)

/-- Both members of every selected pair are positive. -/
theorem shortRoot_pos (i : Fin 8) : typeF4RootPairing_base.IsPos (shortRoot i) :=
  (WordRelations.exceptionalRootPermutation_isPos (longRoot i)).mpr (longRoot_pos i)

/-- On the long-root parameter, the pairing map is the source exponent θ. -/
theorem rootFieldEnd_longRoot (m : ℕ) (i : Fin 8) (t : CoefficientField m) :
    rootFieldEnd m (longRoot i) t = t ^ (2 ^ m) := by
  simp [rootFieldEnd, longRoot_isLong, iterateFrobenius_def]

/-- Squaring the source θ-parameter gives the Tits parameter used in the relations. -/
theorem rootFieldEnd_longRoot_sq (m : ℕ) (i : Fin 8) (t : CoefficientField m) :
    rootFieldEnd m (longRoot i) t ^ 2 = titsEnd m t := by
  rw [rootFieldEnd_longRoot, titsEnd_apply, ← pow_mul, pow_succ]
/-- The root blocks alternate between B₂ and orthogonal mixed-length pairs. -/
theorem rootPair_dot (i : Fin 8) :
    dot (longRoot i).val (shortRoot i).val = if i.val % 2 = 0 then -1 else 0 := by
  fin_cases i <;>
    norm_num [longRoot, shortRoot, relativeRotation, middleReflection, endReflection,
      Equiv.Perm.mul_apply, pow_succ,
      WordRelations.exceptionalRootPermutation_simple_reflection,
      exceptionalRootPermutation_simple, Fin.revPerm, Fin.rev,
      reflection_val, reflectedVector, typeF4SimpleRoot, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]


/-- The mixed root in an even block is the sum of the paired roots. -/
theorem mixedRoot_eq_add (i : Fin 8) (hi : i.val % 2 = 0) :
    (mixedRoot i).val = (longRoot i).val + (shortRoot i).val := by
  have hd : dot (shortRoot i).val (longRoot i).val = -1 := by
    rw [show dot (shortRoot i).val (longRoot i).val =
      dot (longRoot i).val (shortRoot i).val by simp only [dot, mul_comm]]
    simp only [rootPair_dot, hi, ite_true]
  change typeF4RootPairing.root (typeF4RootPairing.reflectionPerm _ _) = _
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root,
    typeF4RootPairing_pairing, typeF4CorootScale_of_pair _ (longRoot_isLong i),
    hd, one_mul, neg_one_smul, sub_neg_eq_add, typeF4RootPairing_root,
    typeF4RootPairing_root, add_comm]

/-- The highest root in an even block is long plus twice short. -/
theorem highRoot_eq_add_two (i : Fin 8) (hi : i.val % 2 = 0) :
    (highRoot i).val = (longRoot i).val + (2 : ℝ) • (shortRoot i).val := by
  have hd : dot (longRoot i).val (shortRoot i).val = -1 := by
    simp only [rootPair_dot, hi, ite_true]
  change typeF4RootPairing.root (typeF4RootPairing.reflectionPerm _ _) = _
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root,
    typeF4RootPairing_pairing, typeF4CorootScale_of_not_pair _ (shortRoot_isShort i), hd]
  simp only [mul_neg, mul_one, neg_smul, sub_neg_eq_add, typeF4RootPairing_root]

end MatrixRelations

open MatrixRelations Binary.FixedGeometry

/-- The displayed middle word is the existing integral B₂ longest-word lift. -/
theorem middleWeylWord_eq_simpleWord (m : ℕ) :
    middleWeylWord m = simpleWord m (sideWord .suzuki) := by
  simp [middleWeylWord, simpleWord, sideWord, mul_assoc]

/-- The integral B₂ braid relation makes the middle word twist-fixed. -/
theorem middleWeylWord_fixed (m : ℕ) :
    (canonicalLocalBlockInput m).twist (middleWeylWord m) = middleWeylWord m := by
  rw [LocalBlockInput.twist_eq_reeAutomorphism, reeAutomorphism_apply,
    middleWeylWord_eq_simpleWord]
  exact sideWord_fixed m .suzuki

/-- Every letter of the middle Weyl word belongs to the Suzuki seed. -/
theorem middleWeylWord_mem_splitSeed (m : ℕ) :
    middleWeylWord m ∈ LargeLocalSeeds.splitSeed m .suzuki := by
  have h := weylLift_mem_seed m .suzuki
  change toSplitGroup m (weylLift m .suzuki) ∈ LargeLocalSeeds.splitSeed m .suzuki at h
  rw [toSplitGroup_weylLift] at h
  rwa [middleWeylWord_eq_simpleWord]

/-- A positive endpoint identifies conjugation by an actual simple Weyl word. -/
theorem simpleWord_conjugate_simple (m : ℕ) (w : List (Fin 4)) (j : Fin 4)
    (r : F4Chevalley.Root) (hr : typeF4RootPairing_base.IsPos r)
    (he : reflectionWord (P := typeF4RootPairing)
      (w.map typeF4RootPairing_baseEquiv) (typeF4SimpleRootIndex j) = r)
    (t : CoefficientField m) :
    simpleWord m w * rootGeneratorInGroup m (typeF4SimpleRootIndex j) t *
      (simpleWord m w)⁻¹ = rootGeneratorInGroup m r t := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, simpleWord_coe]
  exact (WordRelations.rootCurve_of_pos_transport r hr _
    (typeF4RootPairing_baseEquiv j) he t).symm

private theorem paired_conjugate (m : ℕ) (i : Fin 8) (hi : i.val % 2 ≠ 0)
    (w : SplitGroup m) (hw : reeTwist m w = w)
    (hl : ∀ t, w * rootGeneratorInGroup m (typeF4SimpleRootIndex 0) t * w⁻¹ =
      rootGeneratorInGroup m (longRoot i) t) (t : CoefficientField m) :
    w * endRootWord m t * w⁻¹ = rootWord m i t := by
  have hs := congrArg (reeTwist m) (hl t)
  simp only [map_mul, map_inv, hw, reeTwist_rootGenerator, ← rootFieldEnd_apply] at hs
  rw [exceptionalRootPermutation_simple] at hs
  change w * rootGeneratorInGroup m (typeF4SimpleRootIndex 3)
    (rootFieldEnd m (typeF4SimpleRootIndex 0) t) * w⁻¹ = _ at hs
  calc
    _ = (w * rootGeneratorInGroup m (typeF4SimpleRootIndex 0) t * w⁻¹) *
        (w * rootGeneratorInGroup m (typeF4SimpleRootIndex 3)
          (rootFieldEnd m (typeF4SimpleRootIndex 0) t) * w⁻¹) := by
      simp [endRootWord, mul_assoc]
    _ = rootWord m i t := by
      rw [hl, hs]
      simp [rootWord, shortRoot, hi]

/-- The middle longest word carries the eighth paired root curve to the second. -/
theorem middleWeylWord_conjugate_end (m : ℕ) (t : CoefficientField m) :
    middleWeylWord m * rootWord m 7 t * (middleWeylWord m)⁻¹ = rootWord m 1 t := by
  rw [rootWord_end]
  apply paired_conjugate m 1 (by decide)
  · simpa only [LocalBlockInput.twist_eq_reeAutomorphism, reeAutomorphism_apply]
      using middleWeylWord_fixed m
  · intro u
    rw [middleWeylWord_eq_simpleWord]
    apply simpleWord_conjugate_simple m (sideWord .suzuki) 0 _ (longRoot_pos 1)
    rfl

private theorem simpleWord_append (m : ℕ) (u v : List (Fin 4)) :
    simpleWord m (u ++ v) = simpleWord m u * simpleWord m v := by
  simp [simpleWord]

private def fourthWord : List (Fin 4) :=
  sideWord .suzuki ++ sideWord .linear ++ sideWord .suzuki

private theorem fourthWord_fixed (m : ℕ) :
    reeTwist m (simpleWord m fourthWord) = simpleWord m fourthWord := by
  simp only [fourthWord, simpleWord_append, map_mul, sideWord_fixed]

private theorem fourthWord_conjugate_end (m : ℕ) (t : CoefficientField m) :
    simpleWord m fourthWord * endRootWord m t * (simpleWord m fourthWord)⁻¹ =
      rootWord m 3 t := by
  apply paired_conjugate m 3 (by decide) _ (fourthWord_fixed m)
  intro u
  apply simpleWord_conjugate_simple m fourthWord 0 _ (longRoot_pos 3)
  rfl

/-- The fourth curve is additive because it is a Weyl conjugate of the end curve. -/
theorem rootWord_fourth_add (m : ℕ) (t u : CoefficientField m) :
    rootWord m 3 (t + u) = rootWord m 3 t * rootWord m 3 u := by
  rw [← fourthWord_conjugate_end, ← fourthWord_conjugate_end,
    ← fourthWord_conjugate_end, endRootWord_add]
  simp [mul_assoc]

end
end ReeF4.Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
