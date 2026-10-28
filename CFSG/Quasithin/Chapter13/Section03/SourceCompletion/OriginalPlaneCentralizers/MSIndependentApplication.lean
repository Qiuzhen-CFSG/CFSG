module

public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.MSIndependent
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Inspection.Residual

/-!
# The independent MS conclusion on the original escaping component

Choose a Sylow subgroup inside the literal join JQ containing the original
radical Q. The marked perpendicular argument supplies the doubled-natural
whole commutator core and its original radical-centralizer inequality.
The same module marking gives an elementary core of order 64.

The escaping-plane application retains the actual LocalData, the original
prime-to-three residual and marked cubic through LinearThreeRow. It has no
universal binary MS classification premise. The separate chief-factor
argument on Q/V and final plane-centralizer conclusion are not asserted here.

Source: Aschbacher--Smith 13.3.12, printed pp.889--890, especially (*).
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
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

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
