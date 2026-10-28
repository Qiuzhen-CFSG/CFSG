module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialNormalizerEquality
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialCentralCompletion
public import CFSG.Quasithin.ChapterI.Section06To08.Uniqueness
public import CFSG.Quasithin.ChapterI.Section06To08.TightPGroup.CyclicSpan
public import Theory.GroupAction.SmallQuotientCentralization
public import Theory.GroupTheory.FourGroupDisplacement

/-!
# The extraspecial source centralizer and its central four-group

The normalizer equality and the previously proved center containment give
both clauses of 14.7.21 for the original group and flag. The order-four
subgroup chosen after 14.7.25 lies in T and has exact normalizer H.

The first branches of 14.7.26 are then proved. A cyclic choice is TI because
its unique involution generates V₁. A choice centralized by T is centralized
by H = KT, so maximal two-local uniqueness gives the TI property. Otherwise
the choice is elementary, and its order-two quotient by V₁ shows that its
nontrivial T-commutator is exactly V₁. The TI assertion in this last branch
and the subsequent extraspecial exclusion are not asserted here.

Source: Aschbacher–Smith, 14.7.21, 14.7.25 and the opening of 14.7.26,
printed pp.1050–1052; I.6.1, printed p.424.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterI.Section06To08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Both clauses of 14.7.21 on the original group and flag. The centralizer
is that of the actual order-two seed. -/
theorem extraspecial_source_14721
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    normalizer (K F : Set G) = F.H ∧
      F.H = centralizer (F.Vi 1 : Set G) ∧ IsMaximalTwoLocal F.H ∧
      (center ((K F).pCoreIn 2)).map ((K F).pCoreIn 2).subtype ≤
        (center (K F)).map (K F).subtype := by
  obtain ⟨hN,hH⟩ := extraspecial_normalizer_eq_H d h hab structural previous faithful earlier he
  exact ⟨hN,le_antisymm
    (normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide)))
    (Subgroup.centralizer_le_normalizer _),hH,
    extraspecial_core_center_central d h hab structural previous faithful earlier he⟩

/-- The order-four subgroup selected after 14.7.25 has the exact original
normalizer H and lies in T. -/
theorem extraspecial_center_four_normalizer
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ∃ D : Subgroup G, F.Vi 1 ≤ D ∧ D ≤ (center (K F)).map (K F).subtype ∧
      Nat.card D = 4 ∧ D ≤ (T : Subgroup G) ∧ normalizer (D : Set G) = F.H := by
  obtain ⟨D,hZD,hDK,hcard,hHD⟩ := extraspecial_center_four d h hab structural previous faithful earlier he
  have hp : IsPGroup 2 D := isPGroup_iff_card_dvd_pow.mpr ⟨2,by rw [hcard]; decide⟩
  have hne : D ≠ ⊥ := by intro heq; simp [heq] at hcard
  have hmax := (extraspecial_normalizer_eq_H d h hab structural previous faithful earlier he).2
  have hDH : D ≤ F.H := hDK.trans ((map_subtype_le _).trans (K_le_H F))
  have hDT : D ≤ (T : Subgroup G) :=
    (le_pCoreIn_of_normalizes hp hDH hHD).trans
      ((pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))).trans_eq
        (map_subgroupOf_eq_of_le (F.invariant 1)))
  exact ⟨D,hZD,hDK,hcard,hDT,le_antisymm (hmax.2 ⟨D,hne,hp,rfl⟩ hHD) hHD⟩
/-- The source four-group is TI in the cyclic and Sylow-central branches.
The remaining branch is elementary and has exact displacement V₁. -/
theorem extraspecial_center_four_ti_reduction
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ∃ D : Subgroup G, F.Vi 1 ≤ D ∧ D ≤ (center (K F)).map (K F).subtype ∧
      Nat.card D = 4 ∧ D ≤ (T : Subgroup G) ∧ normalizer (D : Set G) = F.H ∧
      (IsTISubgroup D ∨ (IsElementaryAbelian 2 D ∧
        ⁅D,(T : Subgroup G)⁆ = F.Vi 1 ∧ ¬ D ≤ centralizer (T : Set G))) := by
  obtain ⟨D,hZD,hDK,hcard,hDT,hND⟩ := extraspecial_center_four_normalizer
    d h hab structural previous faithful earlier he
  refine ⟨D,hZD,hDK,hcard,hDT,hND,?_⟩
  have hp : IsPGroup 2 D := isPGroup_iff_card_dvd_pow.mpr ⟨2,by rw [hcard]; decide⟩
  have hHnD : F.H ≤ normalizer (D : Set G) := hND.ge
  have hTnD := (F.invariant 1).trans hHnD
  have hZcard : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  by_cases hcyc : IsCyclic D
  · let := hcyc
    exact Or.inl (cyclic_two_TI_of_point_normalizer D (F.Vi 1) hp hZcard hZD hHnD)
  by_cases hc : D ≤ centralizer (T : Set G)
  · left
    have hHC : F.H ≤ centralizer (D : Set G) := by
      rw [residual_product F]
      apply sup_le ?_ (le_centralizer_iff.mp hc)
      apply le_centralizer_iff.mpr
      rw [map_center_subtype_eq_inf_centralizer] at hDK
      exact hDK.trans inf_le_right
    have hmax := (extraspecial_normalizer_eq_H d h hab structural previous faithful earlier he).2
    exact lemma_I_6_1_2 D F.H F.H hp hND.symm hmax le_rfl
      (fun M hM hHM => le_antisymm (hmax.2 hM.1 hHM) hHM) hHC
  right
  have hele : IsElementaryAbelian 2 D := {
    toIsMulCommutative := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hcard
    exponent_dvd_p := ((not_isCyclic_iff_exponent_eq_prime Nat.prime_two hcard).mp hcyc).dvd }
  let Z := (F.Vi 1).subgroupOf D
  have hnZ : Z.Normal := normal_subgroupOf_of_le_normalizer (hDT.trans (F.invariant 1))
  let := hnZ
  have hzcard : Nat.card Z = 2 := (Nat.card_congr (subgroupOfEquivOfLe hZD).toEquiv).trans hZcard
  have hquot : Nat.card (D ⧸ Z) ≤ 2 := by
    have hh := Z.card_mul_index
    rw [hzcard,hcard] at hh
    change Z.index ≤ 2
    omega
  have hcomm : ⁅D,(T : Subgroup G)⁆ ≤ F.Vi 1 :=
    commutator_le_of_normalized_quotient_card_le_two (T : Subgroup G) D (F.Vi 1)
      hTnD (F.invariant 1) hnZ hquot
  have hne : ⁅D,(T : Subgroup G)⁆ ≠ ⊥ := fun heq => hc
    (commutator_eq_bot_iff_le_centralizer.mp heq)
  have hccard := commutator_four_card_of_ne_bot D (T : Subgroup G) hTnD T.isPGroup' hcard hne
  exact ⟨hele,eq_of_le_of_card_ge hcomm (by rw [hZcard,hccard]),hc⟩
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
