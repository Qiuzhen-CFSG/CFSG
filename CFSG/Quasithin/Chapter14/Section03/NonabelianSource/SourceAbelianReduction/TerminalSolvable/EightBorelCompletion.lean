module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.EightBorelExtendedAmalgam
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.CompletionAction

/-!
# Ambient normalizer control for the original eight-field completion

The literal ComponentLift and EightImageRow give a perfect, self-centralizing
completion K join P₂. Its full ambient normalizer is Mc join M, whose derived
subgroup is exactly that completion and whose quotient by it has order dividing
three. The enlarged group is self-normalizing. Its faithful conjugation action
has precisely the original completion as preimage of the inner automorphisms.

The same cubic action on the original marked endpoints extends to this actual
completion, with both endpoint equations retained. No generation of G or
recognition as the standard finite triality group is assumed or asserted.
Those source 14.2.19 and 14.3.6/15 obligations remain with
qt-e-14315-eight-borel-exclusion; the explicit marked input remains owned by
qt-e-1427-eight-amalgam-recognition.

Source: Aschbacher--Smith 14.2.18--19, p.987; F.4.3 and F.4.31, pp.274,290--291.
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

theorem source_eight_marked_completion_normalizer
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G))) :
    centralizer (K : Set G) = centralInvolutions T ∧
      centralizer ((K ⊔ EightLargeParabolic.secondParabolic T M Mc K : Subgroup G) : Set G) = ⊥ ∧
      normalizer ((K ⊔ EightLargeParabolic.secondParabolic T M Mc K : Subgroup G) : Set G) = Mc ⊔ M := by
  have hjoin := source_eight_marked_join_eq hG T hempty hM hu hmany hcard e hK h8 r
  have hH : K ∈ Chapter3.HStar (T : Subgroup G) M := by
    simpa only [hjoin] using
      (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  have rK : EightLargeParabolic.MarkedTriality T M Mc K := hjoin ▸ r
  exact ⟨EightLargeParabolic.source_first_centralizer hG hempty hM hu hmany hcard e hH rK,
    EightLargeParabolic.source_generated_centralizer_eq_bot hG hempty hM hu hmany hcard e hH rK,
    EightLargeParabolic.source_generated_normalizer_eq hG hempty hM hu hmany hcard e hH rK⟩

theorem source_eight_marked_completion_derived
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G))) :
    let B := K ⊔ EightLargeParabolic.secondParabolic T M Mc K
    Group.IsPerfect B ∧ ⁅Mc ⊔ M,Mc ⊔ M⁆ = B ∧ B.relIndex (Mc ⊔ M) ∣ 3 ∧
      normalizer ((Mc ⊔ M : Subgroup G) : Set G) = Mc ⊔ M ∧
      (B = ⊤ ↔ Mc ⊔ M = ⊤) := by
  have hjoin := source_eight_marked_join_eq hG T hempty hM hu hmany hcard e hK h8 r
  have hH : K ∈ Chapter3.HStar (T : Subgroup G) M := by
    simpa only [hjoin] using
      (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  have rK : EightLargeParabolic.MarkedTriality T M Mc K := hjoin ▸ r
  have hd := EightLargeParabolic.source_generated_derived_and_index hG hempty hM hu hmany hcard e hH rK
  exact ⟨EightLargeParabolic.source_generated_perfect hG hempty hM hu hmany hcard e hH rK,
    hd.1,hd.2, EightLargeParabolic.source_extended_self_normalizing hG hempty hM hu hmany hcard e hH rK,
    EightLargeParabolic.source_generated_eq_top_iff hG hempty hM hu hmany hcard e hH rK⟩

theorem source_eight_marked_completion_action
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G))) :
    let B := K ⊔ EightLargeParabolic.secondParabolic T M Mc K
    ∃ ρ : (Mc ⊔ M : Subgroup G) →* MulAut B,
      Function.Injective ρ ∧
      (∀ (x : (Mc ⊔ M : Subgroup G)) (b : B),
        (ρ x b : G) = (x : G) * (b : G) * (x : G)⁻¹) ∧
      (B.subgroupOf (Mc ⊔ M)).map ρ = MulAut.innerSubgroup B ∧
      (MulAut.innerSubgroup B).comap ρ = B.subgroupOf (Mc ⊔ M) := by
  have hjoin := source_eight_marked_join_eq hG T hempty hM hu hmany hcard e hK h8 r
  have hH : K ∈ Chapter3.HStar (T : Subgroup G) M := by
    simpa only [hjoin] using
      (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  have rK : EightLargeParabolic.MarkedTriality T M Mc K := hjoin ▸ r
  exact ⟨EightLargeParabolic.sourceCompletionAction hG hempty hM hu hmany hcard e hH rK,
    EightLargeParabolic.sourceCompletionAction_injective hG hempty hM hu hmany hcard e hH rK,
    EightLargeParabolic.sourceCompletionAction_apply hG hempty hM hu hmany hcard e hH rK,
    EightLargeParabolic.sourceCompletionAction_inner_image hG hempty hM hu hmany hcard e hH rK,
    EightLargeParabolic.sourceCompletionAction_inner_preimage hG hempty hM hu hmany hcard e hH rK⟩


/-- The same faithful cubic extension acts on the whole literal component completion. -/
theorem source_eight_marked_cubic_completion_action
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G)))
    (hne : Mc ≠ K ⊔ (T : Subgroup G)) :
    let H := K ⊔ (T : Subgroup G)
    let P := EightLargeParabolic.secondParabolic T M Mc H
    ∃ (A : Subgroup G) (hAH : A ≤ normalizer (H : Set G))
      (hAP : A ≤ normalizer (P : Set G)),
      A ≤ M ⊓ Mc ∧ Nat.card A = 3 ∧
      Nonempty (RankTwoAmalgam.Iso (EightLargeParabolic.extendedAmalgam Mc M)
        (RankTwoAmalgam.semidirect (EightLargeParabolic.markedCubicAction r A hAH hAP))) ∧
      ∃ η : A →* MulAut (H ⊔ P : Subgroup G), Function.Injective η ∧
        (∀ a x, η a ((EightLargeParabolic.markedCompletion r).left x) =
          (EightLargeParabolic.markedCompletion r).left
            ((EightLargeParabolic.markedCubicAction r A hAH hAP a).left x)) ∧
        (∀ a x, η a ((EightLargeParabolic.markedCompletion r).right x) =
          (EightLargeParabolic.markedCompletion r).right
            ((EightLargeParabolic.markedCubicAction r A hAH hAP a).right x)) := by
  have hH := (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  obtain ⟨A,hAH,hAP,hA,hcardA,hdH,hdP,hMc,hMP,hiso⟩ :=
    EightLargeParabolic.source_extendedAmalgam_split hG hempty hM hu hmany hcard e hH r hne
  have hAJ : A ≤ Mc ⊔ M := (hA.trans inf_le_right).trans le_sup_left
  let η := (EightLargeParabolic.sourceCompletionAction hG hempty hM hu hmany hcard e hH r).comp
    (inclusion hAJ)
  refine ⟨A,hAH,hAP,hA,hcardA,hiso,η,?_,?_,?_⟩
  · exact (EightLargeParabolic.sourceCompletionAction_injective hG hempty hM hu hmany hcard e hH r).comp
      (inclusion_injective hAJ)
  · exact EightLargeParabolic.sourceCompletionAction_left hG hempty hM hu hmany hcard e hH r A hAJ hAH hAP
  · exact EightLargeParabolic.sourceCompletionAction_right hG hempty hM hu hmany hcard e hH r A hAJ hAH hAP

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
