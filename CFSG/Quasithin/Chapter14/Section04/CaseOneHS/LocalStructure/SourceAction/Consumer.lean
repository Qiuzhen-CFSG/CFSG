module

public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS

/-!
# HS recognition with the source center and component constructed

The constructed cyclic-four center and original component enter the literal
LocalStructure assembly and then recognition of the actual HS carrier. Natural
coordinates and 14.3.33 remain explicit source obligations; this conditional
consumer does not establish 14.3.26. The earlier component-conditional interface
is preserved.

Source: Aschbacher--Smith, 14.3.32--33 and the I.4.8 application, pp.1003--1005.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Apply the center construction all the way to the actual HS carrier. -/
theorem recognition_of_natural_component_and_overgroup (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥) (hc : NaturalCoordinates F)
    (component : ∃ K : Subgroup G, K ≤ F.H ∧ (K.subgroupOf F.H).IsCComponent ∧
      F.H = K ⊔ (T : Subgroup G) ∧ F.U = ⁅K.pCoreIn 2, K⁆ ∧
      TildeIndecomposable F K)
    (overgroup : OvergroupStructure L F) (recognition : HigmanSims.Recognition.{u}) :
    Nonempty (G ≃* Sporadic.LeechRelated.HS.Carrier) := by
  obtain ⟨z, _, hz⟩ := type_of_local_and_overgroup d earlier hq chosen alternatives F
    (localStructure_of_natural_component d earlier hq chosen structural alternatives
      F hne hI hc component) overgroup
  exact recognition G ⟨z, V, hz⟩


/-- The actual HS carrier consumer, with all component clauses constructed. -/
theorem recognition_of_natural_and_overgroup (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥) (hc : NaturalCoordinates F)
    (overgroup : OvergroupStructure L F) (recognition : HigmanSims.Recognition.{u}) :
    Nonempty (G ≃* Sporadic.LeechRelated.HS.Carrier) := by
  obtain ⟨z, _, hz⟩ := type_of_local_and_overgroup d earlier hq chosen alternatives F
    (localStructure_of_natural d earlier hq chosen structural alternatives
      F hne hZ hI hc) overgroup
  exact recognition G ⟨z, V, hz⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
