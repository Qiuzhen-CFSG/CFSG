module
public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.RootCalculations.Curves
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
# Linear Weyl transport of the middle Ree involution curves

The fixed end-node Weyl word fixes x₄ and exchanges y₃ with y₅, with the
same field parameter. Small root-coordinate identities and integral matrix
transport prove the formulas inside the actual exceptional-twist fixed model.
The consumer is the middle-tail conjugacy calculation in `DConjugacy.Middle`.

Source: GLS3 Table 2.4 and 2.4.5(d), `refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public section
noncomputable section
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy
attribute [local irreducible] longRoot shortRoot mixedRoot highRoot
open MatrixRelations.LongCommutators

private def sourceIndex : Fin 6 → Fin 24 := ![10, 11, 9, 8, 15, 14]
private def targetIndex : Fin 6 → Fin 24 := ![10, 11, 15, 14, 9, 8]

private theorem linear_action (i : Fin 6) :
    wordAction (sideWord .linear) (R (sourceIndex i)) = R (targetIndex i) := by
  apply Subtype.ext
  simp only [wordAction, sideWord, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, Equiv.Perm.mul_apply, Equiv.Perm.one_apply,
    MatrixRelations.LongCommutators.reflection_val, MatrixRelations.LongCommutators.rval]
  fin_cases i <;> ext k <;> fin_cases k <;>
    norm_num [sourceIndex, targetIndex, MatrixRelations.LongCommutators.reflectedVector,
      V, Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three]

private theorem action_longRoot_3 :
    wordAction (sideWord .linear) (longRoot 3) = longRoot 3 := by
  have h := linear_action 0
  change wordAction (sideWord .linear) (longRoot 3) = longRoot 3 at h
  exact h

private theorem action_shortRoot_3 :
    wordAction (sideWord .linear) (shortRoot 3) = shortRoot 3 := by
  have h := linear_action 1
  change wordAction (sideWord .linear) (shortRoot 3) = shortRoot 3 at h
  exact h

private theorem action_highRoot_2 :
    wordAction (sideWord .linear) (highRoot 2) = highRoot 4 := by
  have h := linear_action 2
  change wordAction (sideWord .linear) (highRoot 2) = highRoot 4 at h
  exact h

private theorem action_mixedRoot_2 :
    wordAction (sideWord .linear) (mixedRoot 2) = mixedRoot 4 := by
  have h := linear_action 3
  change wordAction (sideWord .linear) (mixedRoot 2) = mixedRoot 4 at h
  exact h

private theorem action_highRoot_4 :
    wordAction (sideWord .linear) (highRoot 4) = highRoot 2 := by
  have h := linear_action 4
  change wordAction (sideWord .linear) (highRoot 4) = highRoot 2 at h
  exact h

private theorem action_mixedRoot_4 :
    wordAction (sideWord .linear) (mixedRoot 4) = mixedRoot 2 := by
  have h := linear_action 5
  change wordAction (sideWord .linear) (mixedRoot 4) = mixedRoot 2 at h
  exact h

private theorem fieldEnd_half (m : ℕ) (i : Fin 8) :
    rootFieldEnd m (longRoot i) = halfFrobenius m := by
  simp only [rootFieldEnd, if_pos (MatrixRelations.longRoot_isLong i), halfFrobenius]

theorem linearWeyl_main_fourth (m : ℕ) (a : CoefficientField m) :
    weylLift m .linear * mainElement m 3 a * (weylLift m .linear)⁻¹ =
      mainElement m 3 a := by
  apply toSplitGroup_injective m
  simp only [map_mul, map_inv, toSplitGroup_weylLift, mainElement_coe]
  let f := MulAut.conj (simpleWord m (sideWord .linear))
  change f (rootWord m 3 a) = rootWord m 3 a
  have hc (r : F4Chevalley.Root) (t : CoefficientField m) :
      f (rootGeneratorInGroup m r t) =
        rootGeneratorInGroup m (wordAction (sideWord .linear) r) t :=
    simpleWord_conj_root m _ r t
  simp only [rootWord, show (3 : Fin 8).val % 2 ≠ 0 from by decide, ↓reduceIte,
    map_mul, map_one, fieldEnd_half, hc, action_longRoot_3, action_shortRoot_3]

theorem linearWeyl_central_third (m : ℕ) (a : CoefficientField m) :
    weylLift m .linear * ElementaryTwoBound.centralElement m 2 a *
      (weylLift m .linear)⁻¹ = ElementaryTwoBound.centralElement m 4 a := by
  apply toSplitGroup_injective m
  simp only [map_mul, map_inv, toSplitGroup_weylLift,
    ElementaryTwoBound.centralElement_coe]
  let f := MulAut.conj (simpleWord m (sideWord .linear))
  change f (centralWord m 2 a) = centralWord m 4 a
  have hc (r : F4Chevalley.Root) (t : CoefficientField m) :
      f (rootGeneratorInGroup m r t) =
        rootGeneratorInGroup m (wordAction (sideWord .linear) r) t :=
    simpleWord_conj_root m _ r t
  simp only [centralWord, map_mul, fieldEnd_half, hc,
    action_highRoot_2, action_mixedRoot_2]

theorem linearWeyl_central_fifth (m : ℕ) (a : CoefficientField m) :
    weylLift m .linear * ElementaryTwoBound.centralElement m 4 a *
      (weylLift m .linear)⁻¹ = ElementaryTwoBound.centralElement m 2 a := by
  apply toSplitGroup_injective m
  simp only [map_mul, map_inv, toSplitGroup_weylLift,
    ElementaryTwoBound.centralElement_coe]
  let f := MulAut.conj (simpleWord m (sideWord .linear))
  change f (centralWord m 4 a) = centralWord m 2 a
  have hc (r : F4Chevalley.Root) (t : CoefficientField m) :
      f (rootGeneratorInGroup m r t) =
        rootGeneratorInGroup m (wordAction (sideWord .linear) r) t :=
    simpleWord_conj_root m _ r t
  simp only [centralWord, map_mul, fieldEnd_half, hc,
    action_highRoot_4, action_mixedRoot_4]

end ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy
