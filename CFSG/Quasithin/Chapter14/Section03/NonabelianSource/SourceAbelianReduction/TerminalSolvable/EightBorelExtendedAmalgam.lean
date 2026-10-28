module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.EightBorelCubicExtension
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.ExtendedAmalgam

/-!
# The enlarged amalgam on the original L₂(8) terminal component

Apply the exact split-extension and faithful-completion results to the literal
ComponentLift and EightImageRow, using the proved residual equality and minimality
of K join T. If Mc = K, the enlarged pair is the original marked triality pair.
Otherwise it is a compatible semidirect extension by a faithful cubic action;
the same subgroup A supplements both endpoints and is disjoint from each base.
Its field-automorphism equivalence is the restriction of the original quotient
conjugation action. No containment T ≤ K is assumed.

All ambient source hypotheses and the independent marked realization remain
explicit. Extending this action to the standard finite triality completion,
arbitrary ambient recognition, and original 14.3.6/14.3.15 exclusion remain with
qt-e-14315-eight-borel-exclusion. The marked-realization producer remains
qt-e-1427-eight-amalgam-recognition.

Source: Aschbacher--Smith 14.2.18--19 and 14.3.15, printed pp.987 and 994.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    {F : InvariantFlag T (rankTwoSeed T M) 2} {g : G} {K : Subgroup G}
include hG hempty hM hu hmany hcard e

theorem source_eight_marked_extended_completion
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G))) :
    (EightLargeParabolic.extendedCompletion Mc M).middle.range.normalCore = ⊥ ∧
      ((K ⊔ EightLargeParabolic.secondParabolic T M Mc K).subgroupOf (Mc ⊔ M)).Normal := by
  have hjoin := source_eight_marked_join_eq hG T hempty hM hu hmany hcard e hK h8 r
  have hH : K ∈ Chapter3.HStar (T : Subgroup G) M := by
    simpa only [hjoin] using
      (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  have rK : EightLargeParabolic.MarkedTriality T M Mc K := hjoin ▸ r
  exact ⟨EightLargeParabolic.source_extendedCompletion_corefree
    hG hempty hM hu hmany hcard e hH rK,
    EightLargeParabolic.source_generated_base_normal hG hempty hM hu hmany hcard e hH rK⟩

theorem source_eight_marked_extended_alternatives
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G))) :
    let α := ChapterF.GreenBook.LieModels.Triality.amalgam
      (_root_.Triality.Standard.binaryParameters 1 Nat.zero_lt_one)
    (Mc = K ∧ EightLargeParabolic.secondParabolic T M Mc K = M ∧
      Nonempty (RankTwoAmalgam.Iso (EightLargeParabolic.extendedAmalgam Mc M) α)) ∨
    ∃ (A : Subgroup G) (a : A →* RankTwoAmalgam.Iso α α),
      A ≤ M ⊓ Mc ∧ Nat.card A = 3 ∧
      Disjoint K A ∧ Disjoint (EightLargeParabolic.secondParabolic T M Mc K) A ∧
      Mc = K ⊔ A ∧ M = EightLargeParabolic.secondParabolic T M Mc K ⊔ A ∧
      Function.Injective a ∧
      Nonempty (A ≃* (Theory.PSL2.BinaryField 3 ≃+* Theory.PSL2.BinaryField 3)) ∧
      Nonempty (RankTwoAmalgam.Iso (EightLargeParabolic.extendedAmalgam Mc M)
        (RankTwoAmalgam.semidirect a)) := by
  have hjoin := source_eight_marked_join_eq hG T hempty hM hu hmany hcard e hK h8 r
  have hH : K ∈ Chapter3.HStar (T : Subgroup G) M := by
    simpa only [hjoin] using
      (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  have rK : EightLargeParabolic.MarkedTriality T M Mc K := hjoin ▸ r
  dsimp only
  by_cases he : Mc = K
  · exact Or.inl ⟨he, EightLargeParabolic.source_second_eq_of_partner_eq
      hG hempty hM hu hmany hcard e hH rK he,
      EightLargeParabolic.source_extendedAmalgam_plain hG hempty hM hu hmany hcard e hH rK he⟩
  · obtain ⟨A,hAH,hAP,hA,hcardA,hdK,hdP,hMc,hMP,hiso⟩ :=
      EightLargeParabolic.source_extendedAmalgam_split hG hempty hM hu hmany hcard e hH rK he
    refine Or.inr ⟨A,EightLargeParabolic.markedCubicAction rK A hAH hAP,
      hA,hcardA,hdK,hdP,hMc,hMP,?_,?_,hiso⟩
    · exact EightLargeParabolic.source_markedCubicAction_injective
        hG hempty hM hu hmany hcard e hH rK A (hA.trans inf_le_right) hcardA hdK hAH hAP
    · exact ⟨MulEquiv.ofBijective _ (EightLargeParabolic.source_cubic_field_restriction
        hG hempty hM hu hmany hcard e hH rK A (hA.trans inf_le_right) hcardA hdK)⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
