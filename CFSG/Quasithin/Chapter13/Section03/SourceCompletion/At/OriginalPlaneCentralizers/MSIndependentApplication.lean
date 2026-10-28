module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.MSIndependentApplication
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.At
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Inspection.Residual
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.MSIndependent


/-!
# Original unitary source argument at the same ambient group and Sylow subgroup

This is the ambient-local specialization of `OriginalPlaneCentralizers.MSIndependentApplication`.
Its proof retains the original subgroups, actions, relative Sylow placement,
and quotient maps. Only the earlier 12.2.2 and 12.2.13 inputs are restricted
to the fixed G,T. The universal public API remains in the imported module.
The source argument and reference are recorded there; no additional local
classification or normalizer premise is introduced by this specialization.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V]

/-- Choose the relative Sylow on the original join, preserving its original radical. -/
theorem Context.exists_component_doubled_natural_without_ms (s : Context T L V)
    (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J) :
    ∃ S : Subgroup G, Chapter1.IsSylowIn 2 S (J ⊔ (L ⊔ T).pCoreIn 2) ∧
      (L ⊔ T).pCoreIn 2 ≤ S ∧
      ∃ e : Chapter1.XiQuotient J ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
        HasSectionModel J (msQ J ((L ⊔ T).pCoreIn 2)) ⊥ (linearThreeActor e)
          ((Representation.specialLinearNatural (k := ZMod 2) 3).prod
            (Representation.specialLinearNatural (k := ZMod 2) 3)) ∧
          MSNotCentralizerCore J ((L ⊔ T).pCoreIn 2) S := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let D := J ⊔ Q
  obtain ⟨i⟩ := s.component_has_binaryMS_input d J j
  obtain ⟨P,hP⟩ := i.radical.isPGroup.exists_le_sylow
  let S := (P : Subgroup D).map D.subtype
  have hs : Chapter1.IsSylowIn 2 S D := ⟨P,rfl⟩
  have hqs : Q ≤ S := by
    have hh := map_mono (f := D.subtype) hP
    rwa [map_subgroupOf_eq_of_le (show Q ≤ D from le_sup_right)] at hh
  exact ⟨S,hs,hqs,s.component_doubled_natural_without_ms d J j S hs hqs⟩

/-- The literal original commutator core is elementary of order 64,
without a universal binary classification premise. -/
theorem Context.component_msCore_elementary_card_without_ms (s : Context T L V)
    (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J) :
    IsElementaryAbelian 2 (msQ J ((L ⊔ T).pCoreIn 2)) ∧
      Nat.card (msQ J ((L ⊔ T).pCoreIn 2)) = 64 := by
  obtain ⟨S,_,_,e,he,_⟩ := s.exists_component_doubled_natural_without_ms d J j
  exact ⟨doubled_natural_elementary e he,doubled_natural_card e he⟩

/-- Apply the independent module conclusion to the actual escaping plane centralizer,
retaining the original residual and marked cubic in its terminal row. -/
theorem Context.exists_original_component_doubled_natural_without_ms
    (s : Context T L V) (d : MarkedPlane V)
    (hout : ¬ centralizer (d.A : Set G) ≤ normalizer (L : Set G)) :
    ∃ J : Subgroup G, Nonempty (LocalData T L d J) ∧
      Nonempty (LinearThreeRow T L d J) ∧
      ∃ S : Subgroup G, Chapter1.IsSylowIn 2 S (J ⊔ (L ⊔ T).pCoreIn 2) ∧
        (L ⊔ T).pCoreIn 2 ≤ S ∧
        ∃ e : Chapter1.XiQuotient J ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
          HasSectionModel J (msQ J ((L ⊔ T).pCoreIn 2)) ⊥ (linearThreeActor e)
            ((Representation.specialLinearNatural (k := ZMod 2) 3).prod
              (Representation.specialLinearNatural (k := ZMod 2) 3)) ∧
            MSNotCentralizerCore J ((L ⊔ T).pCoreIn 2) S := by
  obtain ⟨J,⟨j⟩⟩ := s.localExtraction d hout
  exact ⟨J,⟨j⟩,s.linearThreeRow_of_residual d J j (s.local_component_residual d J j),
    s.exists_component_doubled_natural_without_ms d J j⟩

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers
