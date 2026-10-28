module
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy.Reduction
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy.ToD2.WeylCollection
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.WeylGeometry.Orbits
import all Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.MatrixRelations.LongCommutators.RootCalculus
/-!
# Fixed linear Weyl transport on the Ree D section

The linear Weyl representative reverses the seven relative roots of D.
Split-root transport and positive coordinate uniqueness show that it preserves
D, exchanges the Y₁ and Y₇ parameters, and sends the X₆ parameter to X₂.
In particular it carries D₁ into D₂, as needed by the involution transport.
Source: GLS3 Table 2.4, 2.4.5(d), and Lemma 3.3.9.
-/
@[expose] public section
noncomputable section
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy.ToD2
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Parabolics ElementaryTwoBound.RootCalculations
open NormalizedRootCentralizers.CenterExponent
open Parabolics.RadicalCoordinates.FixedCoordinates
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open Parabolics.Binary.FixedGeometry
open LocalBlockInput.PairRigidity.FixedCollection
open OuterElimination MatrixRelations.LongCommutators
-- Root matrices stay atomic during word transport.
attribute [local irreducible] longRoot shortRoot mixedRoot highRoot X

private def sourceIndex : Fin 18 → Fin 24 := ![4, 5, 16, 17, 10, 11, 2, 3, 12, 13, 14, 15, 20, 21, 6, 7, 8, 9]
private def targetIndex : Fin 18 → Fin 24 := ![16, 17, 4, 5, 10, 11, 20, 21, 6, 7, 8, 9, 2, 3, 12, 13, 14, 15]

private def sourceBlock0 : Fin 6 → Fin 24 := ![4, 5, 16, 17, 10, 11]
private def targetBlock0 : Fin 6 → Fin 24 := ![16, 17, 4, 5, 10, 11]
private theorem action_block0 (i : Fin 6) :
    wordAction (sideWord .linear) (R (sourceBlock0 i)) = R (targetBlock0 i) := by
  apply Subtype.ext
  simp only [wordAction, sideWord, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, Equiv.Perm.mul_apply, Equiv.Perm.one_apply,
    MatrixRelations.LongCommutators.reflection_val, MatrixRelations.LongCommutators.rval]
  fin_cases i <;> ext k <;> fin_cases k <;>
    norm_num [sourceBlock0, targetBlock0, MatrixRelations.LongCommutators.reflectedVector,
      V, Matrix.cons_val_two, Matrix.cons_val_three]

private def sourceBlock1 : Fin 6 → Fin 24 := ![2, 3, 12, 13, 14, 15]
private def targetBlock1 : Fin 6 → Fin 24 := ![20, 21, 6, 7, 8, 9]
private theorem action_block1 (i : Fin 6) :
    wordAction (sideWord .linear) (R (sourceBlock1 i)) = R (targetBlock1 i) := by
  apply Subtype.ext
  simp only [wordAction, sideWord, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, Equiv.Perm.mul_apply, Equiv.Perm.one_apply,
    MatrixRelations.LongCommutators.reflection_val, MatrixRelations.LongCommutators.rval]
  fin_cases i <;> ext k <;> fin_cases k <;>
    norm_num [sourceBlock1, targetBlock1, MatrixRelations.LongCommutators.reflectedVector,
      V, Matrix.cons_val_two, Matrix.cons_val_three]

private def sourceBlock2 : Fin 6 → Fin 24 := ![20, 21, 6, 7, 8, 9]
private def targetBlock2 : Fin 6 → Fin 24 := ![2, 3, 12, 13, 14, 15]
private theorem action_block2 (i : Fin 6) :
    wordAction (sideWord .linear) (R (sourceBlock2 i)) = R (targetBlock2 i) := by
  apply Subtype.ext
  simp only [wordAction, sideWord, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, Equiv.Perm.mul_apply, Equiv.Perm.one_apply,
    MatrixRelations.LongCommutators.reflection_val, MatrixRelations.LongCommutators.rval]
  fin_cases i <;> ext k <;> fin_cases k <;>
    norm_num [sourceBlock2, targetBlock2, MatrixRelations.LongCommutators.reflectedVector,
      V, Matrix.cons_val_two, Matrix.cons_val_three]

private theorem linear_action (i : Fin 18) :
    wordAction (sideWord .linear) (R (sourceIndex i)) = R (targetIndex i) := by
  fin_cases i
  · exact action_block0 0
  · exact action_block0 1
  · exact action_block0 2
  · exact action_block0 3
  · exact action_block0 4
  · exact action_block0 5
  · exact action_block1 0
  · exact action_block1 1
  · exact action_block1 2
  · exact action_block1 3
  · exact action_block1 4
  · exact action_block1 5
  · exact action_block2 0
  · exact action_block2 1
  · exact action_block2 2
  · exact action_block2 3
  · exact action_block2 4
  · exact action_block2 5

private theorem linear_split_root (m : ℕ) (i : Fin 18) (t : CoefficientField m) :
    simpleWord m (sideWord .linear) * X m (sourceIndex i) t *
      (simpleWord m (sideWord .linear))⁻¹ = X m (targetIndex i) t := by
  unfold X
  rw [simpleWord_conj_root, linear_action]

private def reflectedWord (m : ℕ) (v : Fin 24 → CoefficientField m) : SplitGroup m :=
  X m 16 (v 4) * (X m 17 (v 5) * (X m 4 (v 16) * (X m 5 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 20 (v 2) * (X m 21 (v 3) * (X m 6 (v 12) * (X m 7 (v 13) * (X m 8 (v 14) * (X m 9 (v 15) * (X m 2 (v 20) * (X m 3 (v 21) * (X m 12 (v 6) * (X m 13 (v 7) * (X m 14 (v 8) * (X m 15 (v 9) * (1))))))))))))))))))

private theorem reflectedWord_mem (m : ℕ) (v : Fin 24 → CoefficientField m) :
    reflectedWord m v ∈ LargeLocalSeeds.splitUnipotent m := by
  have hx (i : Fin 24) (t : CoefficientField m) :
      X m i t ∈ LargeLocalSeeds.splitUnipotent m :=
    Subgroup.subset_closure ⟨R i, t, MatrixRelations.LongCommutators.rpos i, by unfold X; rfl⟩
  unfold reflectedWord
  repeat' apply Subgroup.mul_mem
  all_goals first | exact hx _ _ | exact Subgroup.one_mem _

private theorem linear_word (m : ℕ) (p : PositiveParameters m) (hp : DSupport p) :
    toSplitGroup m (weylLift m .linear * wordElement m p * (weylLift m .linear)⁻¹) =
      reflectedWord m (parameters m p) := by
  rcases hp with ⟨hp0, hm0, hm2⟩
  simp only [map_mul, map_inv, toSplitGroup_weylLift, wordElement_coe, positiveWord_split]
  let f := MulAut.conj (simpleWord m (sideWord .linear))
  change f (splitWord m (parameters m p)) = _
  have hc (i : Fin 18) (t : CoefficientField m) :
      f (X m (sourceIndex i) t) = X m (targetIndex i) t := linear_split_root m i t
  have hs (v : Fin 24 → CoefficientField m) :
      f (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))) = reflectedWord m v := by
    simp only [map_mul, map_one, reflectedWord]
    simp only [(show f (X m 4 (v 4)) = X m 16 (v 4) from hc 0 (v 4)),
      (show f (X m 5 (v 5)) = X m 17 (v 5) from hc 1 (v 5)),
      (show f (X m 16 (v 16)) = X m 4 (v 16) from hc 2 (v 16)),
      (show f (X m 17 (v 17)) = X m 5 (v 17) from hc 3 (v 17)),
      (show f (X m 10 (v 10)) = X m 10 (v 10) from hc 4 (v 10)),
      (show f (X m 11 (v 11)) = X m 11 (v 11) from hc 5 (v 11)),
      (show f (X m 2 (v 2)) = X m 20 (v 2) from hc 6 (v 2)),
      (show f (X m 3 (v 3)) = X m 21 (v 3) from hc 7 (v 3)),
      (show f (X m 12 (v 12)) = X m 6 (v 12) from hc 8 (v 12)),
      (show f (X m 13 (v 13)) = X m 7 (v 13) from hc 9 (v 13)),
      (show f (X m 14 (v 14)) = X m 8 (v 14) from hc 10 (v 14)),
      (show f (X m 15 (v 15)) = X m 9 (v 15) from hc 11 (v 15)),
      (show f (X m 20 (v 20)) = X m 2 (v 20) from hc 12 (v 20)),
      (show f (X m 21 (v 21)) = X m 3 (v 21) from hc 13 (v 21)),
      (show f (X m 6 (v 6)) = X m 12 (v 6) from hc 14 (v 6)),
      (show f (X m 7 (v 7)) = X m 13 (v 7) from hc 15 (v 7)),
      (show f (X m 8 (v 8)) = X m 14 (v 8) from hc 16 (v 8)),
      (show f (X m 9 (v 9)) = X m 15 (v 9) from hc 17 (v 9))]
  simpa only [splitWord, parameters, hp0, hm0, hm2, map_zero, zero_mul,
    zero_add, xz, one_mul, Matrix.cons_val_zero, Matrix.cons_val, Fin.reduceFinMk]
    using hs (parameters m p)

/-- The fixed linear reflection preserves D and exchanges its endpoint data. -/
theorem linear_transport (m : ℕ) (p : PositiveParameters m) (hp : DSupport p) :
    ∃ q : PositiveParameters m, DSupport q ∧
      weylLift m .linear * wordElement m p * (weylLift m .linear)⁻¹ = wordElement m q ∧
      q.central 0 = p.central 2 ∧ q.pair 1 = p.pair 2 := by
  have hmem : weylLift m .linear * wordElement m p * (weylLift m .linear)⁻¹ ∈
      unipotent m := by
    change toSplitGroup m _ ∈ LargeLocalSeeds.splitUnipotent m
    rw [linear_word m p hp]
    exact reflectedWord_mem m _
  obtain ⟨q, hq⟩ := exists_positiveWord m _ hmem
  have he := WeylCollection.coordinates m (parameters m p) (parameters m q) (by
    change reflectedWord m (parameters m p) = _
    rw [← linear_word m p hp, hq, positiveWord_split])
  change q.main 0 = 0 ∧ q.main 2 = 0 ∧ q.pair 0 = 0 ∧
    q.central 0 = p.central 2 ∧ q.pair 1 = p.pair 2 at he
  refine ⟨q, ⟨he.2.2.1, he.1, he.2.1⟩, ?_, he.2.2.2⟩
  apply toSplitGroup_injective m
  simpa only [wordElement_coe] using hq

end ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy.ToD2
