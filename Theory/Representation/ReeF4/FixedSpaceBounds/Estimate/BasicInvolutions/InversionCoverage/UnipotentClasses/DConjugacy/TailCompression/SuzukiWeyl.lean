module
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy.Reduction
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.WeylGeometry.Orbits
-- Internal use of the already checked split-root coordinate table avoids
-- repeating its expensive geometric calculation. No private name is exported.
import all Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.MatrixRelations.LongCommutators.RootCalculus
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open ReeF4 ReeF4.Parabolics
open ReeF4.Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open ReeF4.Parabolics.Binary.FixedGeometry
open ReeF4.LocalBlockInput.PairRigidity.FixedCollection
open ReeF4.Parabolics.RadicalCoordinates.FixedCoordinates
open ReeF4.NormalizedRootCentralizers.CenterExponent
open MatrixRelations
/-!
# Suzuki Weyl transport of the five-coordinate Ree tail

The fixed middle-node Weyl word negates the last two Euclidean root
coordinates. It exchanges x₆ with x₄ and y₇ with y₃, fixing y₅, with
unchanged field parameters. Transport of actual split-root generators
and tail commutation give the formula in the fixed Ree model.
This is the final transport used by `TailCompression`.

Source: GLS3 Table 2.4 and 2.4.5(d), `refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public section
noncomputable section
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy
attribute [local irreducible] longRoot shortRoot mixedRoot highRoot
open MatrixRelations.LongCommutators

namespace TailCompression
open ElementaryTwoBound ElementaryTwoBound.RootCalculations
private def sourceIndex : Fin 10 → Fin 24 := ![16, 17, 10, 11, 15, 14, 21, 20, 9, 8]
private def targetIndex : Fin 10 → Fin 24 := ![10, 11, 16, 17, 15, 14, 9, 8, 21, 20]

private theorem suzuki_action_val (r : F4Chevalley.Root) :
    (wordAction (sideWord .suzuki) r).val = ![r.val 0, r.val 1, -r.val 2, -r.val 3] := by
  simp only [wordAction, sideWord, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, Equiv.Perm.mul_apply, Equiv.Perm.one_apply,
    MatrixRelations.LongCommutators.reflection_val]
  ext k
  fin_cases k <;> simp [MatrixRelations.LongCommutators.reflectedVector]

private theorem suzuki_action_0 :
    wordAction (sideWord .suzuki) (R 16) = R 10 := by
  apply Subtype.ext
  simp only [suzuki_action_val, MatrixRelations.LongCommutators.rval]
  ext z
  fin_cases z <;> norm_num [V, Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three]

private theorem suzuki_action_1 :
    wordAction (sideWord .suzuki) (R 17) = R 11 := by
  apply Subtype.ext
  simp only [suzuki_action_val, MatrixRelations.LongCommutators.rval]
  ext z
  fin_cases z <;> norm_num [V, Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three]

private theorem suzuki_action_2 :
    wordAction (sideWord .suzuki) (R 10) = R 16 := by
  apply Subtype.ext
  simp only [suzuki_action_val, MatrixRelations.LongCommutators.rval]
  ext z
  fin_cases z <;> norm_num [V, Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three]

private theorem suzuki_action_3 :
    wordAction (sideWord .suzuki) (R 11) = R 17 := by
  apply Subtype.ext
  simp only [suzuki_action_val, MatrixRelations.LongCommutators.rval]
  ext z
  fin_cases z <;> norm_num [V, Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three]

private theorem suzuki_action_4 :
    wordAction (sideWord .suzuki) (R 15) = R 15 := by
  apply Subtype.ext
  simp only [suzuki_action_val, MatrixRelations.LongCommutators.rval]
  ext z
  fin_cases z <;> norm_num [V, Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three]

private theorem suzuki_action_5 :
    wordAction (sideWord .suzuki) (R 14) = R 14 := by
  apply Subtype.ext
  simp only [suzuki_action_val, MatrixRelations.LongCommutators.rval]
  ext z
  fin_cases z <;> norm_num [V, Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three]

private theorem suzuki_action_6 :
    wordAction (sideWord .suzuki) (R 21) = R 9 := by
  apply Subtype.ext
  simp only [suzuki_action_val, MatrixRelations.LongCommutators.rval]
  ext z
  fin_cases z <;> norm_num [V, Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three]

private theorem suzuki_action_7 :
    wordAction (sideWord .suzuki) (R 20) = R 8 := by
  apply Subtype.ext
  simp only [suzuki_action_val, MatrixRelations.LongCommutators.rval]
  ext z
  fin_cases z <;> norm_num [V, Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three]

private theorem suzuki_action_8 :
    wordAction (sideWord .suzuki) (R 9) = R 21 := by
  apply Subtype.ext
  simp only [suzuki_action_val, MatrixRelations.LongCommutators.rval]
  ext z
  fin_cases z <;> norm_num [V, Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three]

private theorem suzuki_action_9 :
    wordAction (sideWord .suzuki) (R 8) = R 20 := by
  apply Subtype.ext
  simp only [suzuki_action_val, MatrixRelations.LongCommutators.rval]
  ext z
  fin_cases z <;> norm_num [V, Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three]

private theorem suzuki_action (i : Fin 10) :
    wordAction (sideWord .suzuki) (R (sourceIndex i)) = R (targetIndex i) := by
  fin_cases i
  · exact suzuki_action_0
  · exact suzuki_action_1
  · exact suzuki_action_2
  · exact suzuki_action_3
  · exact suzuki_action_4
  · exact suzuki_action_5
  · exact suzuki_action_6
  · exact suzuki_action_7
  · exact suzuki_action_8
  · exact suzuki_action_9

private theorem fieldEnd_half (m : ℕ) (i : Fin 8) :
    rootFieldEnd m (longRoot i) = halfFrobenius m := by
  simp only [rootFieldEnd, if_pos (MatrixRelations.longRoot_isLong i), halfFrobenius]

private theorem suzuki_main_5 (m : ℕ) (a : CoefficientField m) :
    weylLift m .suzuki * mainElement m 5 a * (weylLift m .suzuki)⁻¹ =
      mainElement m 3 a := by
  apply toSplitGroup_injective m
  simp only [map_mul, map_inv, toSplitGroup_weylLift, mainElement_coe]
  let f := MulAut.conj (simpleWord m (sideWord .suzuki))
  change f (rootWord m 5 a) = rootWord m 3 a
  have hc (r : F4Chevalley.Root) (t : CoefficientField m) :
      f (rootGeneratorInGroup m r t) =
        rootGeneratorInGroup m (wordAction (sideWord .suzuki) r) t :=
    simpleWord_conj_root m _ r t
  have h1 : wordAction (sideWord .suzuki) (longRoot 5) = longRoot 3 := suzuki_action 0
  have h2 : wordAction (sideWord .suzuki) (shortRoot 5) = shortRoot 3 := suzuki_action 1
  simp only [rootWord, show (5 : Fin 8).val % 2 ≠ 0 from by decide, show (3 : Fin 8).val % 2 ≠ 0 from by decide, ↓reduceIte, map_mul, map_one, fieldEnd_half, hc, h1, h2]

private theorem suzuki_main_3 (m : ℕ) (a : CoefficientField m) :
    weylLift m .suzuki * mainElement m 3 a * (weylLift m .suzuki)⁻¹ =
      mainElement m 5 a := by
  apply toSplitGroup_injective m
  simp only [map_mul, map_inv, toSplitGroup_weylLift, mainElement_coe]
  let f := MulAut.conj (simpleWord m (sideWord .suzuki))
  change f (rootWord m 3 a) = rootWord m 5 a
  have hc (r : F4Chevalley.Root) (t : CoefficientField m) :
      f (rootGeneratorInGroup m r t) =
        rootGeneratorInGroup m (wordAction (sideWord .suzuki) r) t :=
    simpleWord_conj_root m _ r t
  have h1 : wordAction (sideWord .suzuki) (longRoot 3) = longRoot 5 := suzuki_action 2
  have h2 : wordAction (sideWord .suzuki) (shortRoot 3) = shortRoot 5 := suzuki_action 3
  simp only [rootWord, show (3 : Fin 8).val % 2 ≠ 0 from by decide, show (5 : Fin 8).val % 2 ≠ 0 from by decide, ↓reduceIte, map_mul, map_one, fieldEnd_half, hc, h1, h2]

private theorem suzuki_central_4 (m : ℕ) (a : CoefficientField m) :
    weylLift m .suzuki * centralElement m 4 a * (weylLift m .suzuki)⁻¹ =
      centralElement m 4 a := by
  apply toSplitGroup_injective m
  simp only [map_mul, map_inv, toSplitGroup_weylLift, centralElement_coe]
  let f := MulAut.conj (simpleWord m (sideWord .suzuki))
  change f (centralWord m 4 a) = centralWord m 4 a
  have hc (r : F4Chevalley.Root) (t : CoefficientField m) :
      f (rootGeneratorInGroup m r t) =
        rootGeneratorInGroup m (wordAction (sideWord .suzuki) r) t :=
    simpleWord_conj_root m _ r t
  have h1 : wordAction (sideWord .suzuki) (highRoot 4) = highRoot 4 := suzuki_action 4
  have h2 : wordAction (sideWord .suzuki) (mixedRoot 4) = mixedRoot 4 := suzuki_action 5
  simp only [centralWord, map_mul, fieldEnd_half, hc, h1, h2]

private theorem suzuki_central_6 (m : ℕ) (a : CoefficientField m) :
    weylLift m .suzuki * centralElement m 6 a * (weylLift m .suzuki)⁻¹ =
      centralElement m 2 a := by
  apply toSplitGroup_injective m
  simp only [map_mul, map_inv, toSplitGroup_weylLift, centralElement_coe]
  let f := MulAut.conj (simpleWord m (sideWord .suzuki))
  change f (centralWord m 6 a) = centralWord m 2 a
  have hc (r : F4Chevalley.Root) (t : CoefficientField m) :
      f (rootGeneratorInGroup m r t) =
        rootGeneratorInGroup m (wordAction (sideWord .suzuki) r) t :=
    simpleWord_conj_root m _ r t
  have h1 : wordAction (sideWord .suzuki) (highRoot 6) = highRoot 2 := suzuki_action 6
  have h2 : wordAction (sideWord .suzuki) (mixedRoot 6) = mixedRoot 2 := suzuki_action 7
  simp only [centralWord, map_mul, fieldEnd_half, hc, h1, h2]

private theorem suzuki_central_2 (m : ℕ) (a : CoefficientField m) :
    weylLift m .suzuki * centralElement m 2 a * (weylLift m .suzuki)⁻¹ =
      centralElement m 6 a := by
  apply toSplitGroup_injective m
  simp only [map_mul, map_inv, toSplitGroup_weylLift, centralElement_coe]
  let f := MulAut.conj (simpleWord m (sideWord .suzuki))
  change f (centralWord m 2 a) = centralWord m 6 a
  have hc (r : F4Chevalley.Root) (t : CoefficientField m) :
      f (rootGeneratorInGroup m r t) =
        rootGeneratorInGroup m (wordAction (sideWord .suzuki) r) t :=
    simpleWord_conj_root m _ r t
  have h1 : wordAction (sideWord .suzuki) (highRoot 2) = highRoot 6 := suzuki_action 8
  have h2 : wordAction (sideWord .suzuki) (mixedRoot 2) = mixedRoot 6 := suzuki_action 9
  simp only [centralWord, map_mul, fieldEnd_half, hc, h1, h2]

private theorem commute_main (m : ℕ) (a b : CoefficientField m) :
    Commute (mainElement m 5 a) (mainElement m 3 b) := by
  change _ * _ = _ * _
  apply toSplitGroup_injective m
  simp only [map_mul, mainElement_coe]
  change Commute (rootWord m 5 a) (rootWord m 3 b)
  have h1 : rootWord m 5 a = X m 16 a * X m 17 (halfFrobenius m a) := by
    simp only [rootWord, fieldEnd_half]
    exact mul_one _
  have h2 : rootWord m 3 b = X m 10 b * X m 11 (halfFrobenius m b) := by
    simp only [rootWord, fieldEnd_half]
    exact mul_one _
  rw [h1, h2]
  apply Commute.mul_right <;> apply Commute.mul_left
  all_goals exact xc m _ _ (by norm_num [V, dot, Fin.sum_univ_four,
    Matrix.cons_val_two, Matrix.cons_val_three]) _ _

private theorem commute_central (m : ℕ) (a b : CoefficientField m) :
    Commute (centralElement m 6 a) (centralElement m 2 b) := by
  change _ * _ = _ * _
  apply toSplitGroup_injective m
  simp only [map_mul, centralElement_coe]
  change Commute (centralWord m 6 a) (centralWord m 2 b)
  have h1 : centralWord m 6 a = X m 21 a * X m 20 (halfFrobenius m a) := by
    simp only [centralWord, fieldEnd_half]
    rfl
  have h2 : centralWord m 2 b = X m 9 b * X m 8 (halfFrobenius m b) := by
    simp only [centralWord, fieldEnd_half]
    rfl
  rw [h1, h2]
  apply Commute.mul_right <;> apply Commute.mul_left
  all_goals exact xc m _ _ (by norm_num [V, dot, Fin.sum_univ_four,
    Matrix.cons_val_two, Matrix.cons_val_three]) _ _

/-- The middle-node fixed Weyl representative swaps both outside pairs of
coordinates and fixes the fifth central curve. -/
theorem suzukiWeyl_tail (m : ℕ) (a b c d e : CoefficientField m) :
    weylLift m .suzuki * tailElement m ![a, b, c, d, e] * (weylLift m .suzuki)⁻¹ =
      tailElement m ![b, a, c, e, d] := by
  let f := MulAut.conj (weylLift m .suzuki)
  change f (tailElement m ![a, b, c, d, e]) = _
  have h0 := suzuki_main_5 m a
  have h1 := suzuki_main_3 m b
  have h2 := suzuki_central_4 m c
  have h3 := suzuki_central_6 m d
  have h4 := suzuki_central_2 m e
  change f (mainElement m 5 a) = _ at h0
  change f (mainElement m 3 b) = _ at h1
  change f (centralElement m 4 c) = _ at h2
  change f (centralElement m 6 d) = _ at h3
  change f (centralElement m 2 e) = _ at h4
  simp only [tailElement_eq_product, Matrix.cons_val_zero, Matrix.cons_val,
    map_mul, h0, h1, h2, h3, h4]
  rw [(commute_main m b a).eq.symm]
  simp only [mul_assoc]
  rw [(commute_central m e d).eq.symm]

end TailCompression
end ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy
