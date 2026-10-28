module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Max2Reducibility.MatrixConditions
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Max2Reducibility.CubicStructure.Alignment
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.LinearNormalizer.CoreRecognition
public import Theory.Mathieu.M22.Properties.Simplicity
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore
public import Theory.GroupTheory.PCorePrimeToIndex

/-!
# The cubic three-core of the actual max2 matrix quotient

The certified basis and generator changes identify the published quotient
matrices with `TwoCoreLinearModel.actionGroup`. Its literal commutator subgroup
is perfect, with central quotient the concrete M₂₂ and center of order three.
Thus its three-core is exactly that center. The independently certified order
2661120 makes this commutator subgroup have index two. The whole group's
three-core therefore lies in the commutator's three-core; characteristicity
gives the reverse inclusion.

All normality is taken inside the action group. No equality with the full
involution centralizer, or simplicity of ambient J₄, is used.

Source: Aschbacher–Smith, Proposition 1.3.4, printed p.511/PDF p.528 of
`refs/quasithin.pdf`; GLS3 Table 5.3i. The concrete ATLAS data and their
attribution are retained in the imported matrix model modules.
-/

public section
open Subgroup
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Adequate.Max2

private theorem core_center_card : Nat.card (center derivedGroup) = 3 := by
  rw [center_derivedGroup_eq_zpowers, Nat.card_zpowers]
  exact orderOf_eq_prime coreScalar_pow_three coreScalar_ne_one

private theorem core_card : Nat.card derivedGroup = 1330560 := by
  have hq : Nat.card (derivedGroup ⧸ center derivedGroup) = 443520 :=
    (Nat.card_congr derivedQuotientEquivM22.toEquiv).trans Sporadic.Mathieu.m22_order
  have h := (center derivedGroup).card_mul_index
  rw [index_eq_card, core_center_card, hq] at h
  exact h.symm

private theorem core_threeCore_eq_center : pCore 3 derivedGroup = center derivedGroup := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : IsSimpleGroup Sporadic.Mathieu.M22 := Sporadic.Mathieu.m22_isSimpleGroup
  let : Theory.GroupTheory.IsQuasisimple derivedGroup :=
    { simple := derivedQuotientEquivM22.isSimpleGroup }
  apply le_antisymm (Theory.GroupTheory.IsQuasisimple.pCore_le_center 3)
  exact le_sSup ⟨inferInstance, IsPGroup.of_card (p := 3) (n := 1)
    (by simpa using core_center_card)⟩

private noncomputable def internalCoreEquiv : commutator actionGroup ≃* derivedGroup :=
  ((commutator actionGroup).equivMapOfInjective actionGroup.subtype
    actionGroup.subtype_injective).trans
    (MulEquiv.subgroupCongr (map_subtype_commutator actionGroup))

private theorem internalCore_card : Nat.card (commutator actionGroup) = 1330560 :=
  (Nat.card_congr internalCoreEquiv.toEquiv).trans core_card

private theorem internalCore_threeCore_card :
    Nat.card (pCore 3 (commutator actionGroup)) = 3 := by
  rw [← card_map_of_injective (f := internalCoreEquiv.toMonoidHom) internalCoreEquiv.injective,
    pCore_map_iso, core_threeCore_eq_center]
  exact core_center_card

private theorem actionGroup_card : Nat.card actionGroup = 2661120 :=
  (Nat.card_congr matrixEquivActionGroup.symm.toEquiv).trans involutionMatrixQuotient_card

private theorem internalCore_index : (commutator actionGroup).index = 2 := by
  have h := (commutator actionGroup).card_mul_index
  rw [internalCore_card, actionGroup_card] at h
  omega

private theorem actionGroup_threeCore_eq :
    pCore 3 actionGroup =
      (pCore 3 (commutator actionGroup)).map (commutator actionGroup).subtype := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply le_antisymm
  · exact pCore_le_map_pCore_of_prime_not_dvd_index _ (by rw [internalCore_index]; decide)
  · exact le_sSup ⟨inferInstance, pCore_isPGroup.map _⟩

/-- The three-core of the actual max2 quotient matrices has order three. -/
theorem matrix_threeCore_card : Nat.card (pCore 3 MatrixGroup) = 3 := by
  rw [← card_map_of_injective (f := matrixEquivActionGroup.toMonoidHom) matrixEquivActionGroup.injective,
    pCore_map_iso, actionGroup_threeCore_eq,
    card_map_of_injective (commutator actionGroup).subtype_injective]
  exact internalCore_threeCore_card

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Adequate.Max2
