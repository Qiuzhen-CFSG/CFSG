module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalHStarSourceResidualFive
import all CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalHStarSourceFiveExclusion

/-!
# Excluding the equal H-star overcomponent on a chosen module

The quadratic TI-pair obstruction applies to every elementary subgroup of
O₂(H) centralized by O₂(H). When the residual is its own maximal overcomponent,
its actual chosen Irr⁺ module has the orthogonal A₅ action. Odd-degree central
cover rigidity lifts this marking to the whole chosen module, which lies in
O₂(H) and is centralized by it. The quadratic obstruction excludes this case.

The original guarded nonsolvable H-star construction therefore has a proper
A₇ overcomponent, retaining the actual A₅ residual quotient, O₂,Z quotient of
the overcomponent, and T-invariance and dimensions of all original choices.
The remaining proper-overcomponent TI exclusion and final natural assembly
stay with qt-d-12213-hstar-natural. No whole omega-span decomposition is assumed.

The internal import intentionally reuses the quotient and section transports
from FiveExclusion within this source proof family; their public boundary is
unchanged. Source: Aschbacher–Smith, 12.2.7 and 12.2.19, printed pp.797–798,801–802.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H X : Subgroup G}

/-- The quadratic TI-pair obstruction applies to any original core subgroup
centralized by the core, not only to a subgroup of the omega span. -/
theorem chosen_hstar_no_five_natural_model_on_core_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hVN : V ≤ (pResidual 2 H).map H.subtype ⊔ H.pCoreIn 2)
    (S : Subgroup G) [IsElementaryAbelian 2 S]
    (hSK : S ≤ (pResidual 2 H).map H.subtype) (hSQ : S ≤ H.pCoreIn 2)
    (hQS : H.pCoreIn 2 ≤ centralizer (S : Set G))
    (hmodel : Chapter6.Source.IsConjugationModel ((pResidual 2 H).map H.subtype) S
      (alternatingNatural 5)) : False := by
  let K := (pResidual 2 H).map H.subtype
  let Q := H.pCoreIn 2
  let N := K ⊔ Q
  have hKH : K ≤ H := map_subtype_le _
  have hHQ : H ≤ normalizer (Q : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  obtain ⟨e,b,hb⟩ := hmodel
  let eK : pResidual 2 H ≃* K := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  let eR := (QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK)).trans e
  have hm := chosen_movement_of_quotient_rank_at h D structural hnone hTI hH
    (chosen_hstar_quotient_rank_of_residual_identification_at h D structural hTI hH (fun _ => ⟨eR⟩))
  obtain ⟨f,hf,hker,hfk⟩ := core_join_projection K Q (hKH.trans hHQ) residual_core_intersection e
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let C := model_section K S hSK (alternatingNatural 5) e b hb
  let C' := extend_section K Q S (alternatingNatural 5) q C hQS f hfk hker
  have hm' : ¬ V.subgroupOf N ≤ f.ker := by
    intro hv
    apply hm
    intro v hv'
    exact hker.le (hv (show (⟨v,hVN hv'⟩ : N) ∈ V.subgroupOf N from hv'))
  let E := BinaryPermutation.coreEquivNatural (Fin 5) (by decide)
  exact chosen_hstar_no_five_permutation_summand_at h D structural hTI hH N
    (sup_le hKH (pCoreIn_le 2 H)) hVN f hf hker.le hm' _ S ⊥ hSQ C'
    E.toLinearMap E.injective (fun a v =>
      BinaryPermutation.coreEquivNatural_equivariant (Fin 5) (by decide) a.val v)

/-- The equal-overcomponent case is excluded on an actual chosen module.
The original Irr⁺ choice lifts from its odd alternating quotient to the whole
module, so no decomposition of the whole omega span is assumed. -/
theorem HStarGeneratingComponent.not_hypothesis1223_at
    (C : HStarGeneratingComponent T L H X)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hX : Hypothesis1223 KnownSimple.IsKnownSimple T X) : False := by
  obtain ⟨⟨W,⟨E⟩⟩⟩ := (structural X hX).2.1
  let := E.actionCentralizer_normal
  obtain ⟨⟨e⟩,⟨a⟩⟩ := C.five_of_eq_at h D structural modules hTI hH hX rfl E
  obtain ⟨b⟩ := E.fullAction_of_odd_alternating_quotient (by decide) (by decide) a
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hs : IsSimpleGroup (X ⧸ pCore 2 X) := e.isSimpleGroup
  let c : ActionEquiv E.quotientAction (alternatingNatural 5) := {
    groupEquiv := (E.coreToFaithfulEquiv hs).trans b.groupEquiv
    linearEquiv := b.linearEquiv
    intertwines := by
      intro g v
      have hc := b.intertwines (E.coreToFaithful g) v
      change b.linearEquiv ((E.faithfulAction.comp E.coreToFaithful) g v) = _ at hc
      rwa [E.faithfulAction_comp_coreToFaithful] at hc }
  have hr := C.eq_residual_of_normalized (structural X hX).1
  let eK : pResidual 2 H ≃* X :=
    ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective).trans
      (MulEquiv.subgroupCongr hr.symm)
  let eR := (QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK)).trans e
  have hVN := chosen_hstar_le_residual_join_core_at h D structural hH eR
  let := E.elementary
  apply chosen_hstar_no_five_natural_model_on_core_at h D structural hnone hTI hH hVN W
  · rw [←hr]
    exact (chosen_le_component_core_at hX E structural).trans (pCoreIn_le 2 X)
  · simpa only [C.generates] using E.le_core
  · simpa only [C.generates] using E.core_centralizes
  · simpa only [←hr] using E.conjugationModel_of_quotientAction c

/-- In the original guarded nonsolvable H-star branch only the proper A₇
overcomponent survives; its literal central quotient and all chosen dimensions
are those in source 12.2.7(3ii). -/
theorem chosen_hstar_proper_seven_overcomponent_of_many_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hs : ¬ Group.IsSolvable H) :
    ∃ X Y : Subgroup G, HStarGeneratingComponent T L H X ∧
      X = (pResidual 2 H).map H.subtype ∧ X < Y ∧
      Hypothesis1223 KnownSimple.IsKnownSimple T Y ∧
      Nonempty ((X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 5)) ∧
      Nonempty ((Y ⧸ centralPreimage (pCore 2 Y)) ≃* alternatingGroup (Fin 7)) ∧
      ∀ (W : Subgroup G) (E : ChosenModule T Y W),
        (T : Subgroup G) ≤ normalizer (W : Set G) ∧
        (Module.finrank (ZMod 2) E.space = 4 ∨ Module.finrank (ZMod 2) E.space = 6) := by
  obtain ⟨X,Y,C,hr,hXY,hY⟩ := chosen_hstar_exists_residual_overcomponent_of_many_at
    h D structural modules hmany hnone hTI hH hs
  have hlt : X < Y := lt_of_le_of_ne hXY (by
    intro he
    exact C.not_hypothesis1223_at h D structural modules hnone hTI hH (he.symm ▸ hY))
  obtain ⟨⟨W,⟨E⟩⟩⟩ := (structural Y hY).2.1
  exact ⟨X,Y,C,hr,hlt,hY,C.five_of_overcomponent_at h D structural modules hTI hH hXY hY,
    (C.proper_seven_source_at h D structural modules hTI hH hlt hY E).1,
    fun _ E => (C.proper_seven_source_at h D structural modules hTI hH hlt hY E).2⟩

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
