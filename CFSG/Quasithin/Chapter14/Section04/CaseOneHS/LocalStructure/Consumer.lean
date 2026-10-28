module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS

/-!
# HS recognition after the local action has been identified

This consumer constructs LocalStructure using the actual Frattini theorem,
natural coordinates and cyclic center, and supplies it to the published HS
assembly. Centerlessness and ActionStructure remain explicit until their
source proofs are supplied by the LocalStructure owner. OvergroupStructure
and I.4.8 recognition remain with the parent HS assembly.

Source: Aschbacher--Smith, 14.3.31--33 and the final application of I.4.8,
printed pp.1002--1005. No unconditional HS recognition is asserted here.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Feed the constructed local structure into the literal type-HS application. -/
theorem type_of_centerless_action_and_overgroup (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hcenterless : Chapter12.Section08.centerIn (F.I₂ L) = ⊥) (action : ActionStructure F)
    (overgroup : OvergroupStructure L F) :
    ∃ z : G, F.Vi 1 = zpowers z ∧ HigmanSims.TypeAt z V :=
  type_of_local_and_overgroup d earlier hq chosen alternatives F
    (localStructure_of_centerless_action d earlier hq chosen structural alternatives
      F hne hcenterless action) overgroup

/-- The same constructed local structure feeds the actual HS carrier recognition. -/
theorem recognition_of_centerless_action_and_overgroup (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hcenterless : Chapter12.Section08.centerIn (F.I₂ L) = ⊥) (action : ActionStructure F)
    (overgroup : OvergroupStructure L F) (recognition : HigmanSims.Recognition.{u}) :
    Nonempty (G ≃* Sporadic.LeechRelated.HS.Carrier) := by
  obtain ⟨z, _, hz⟩ := type_of_centerless_action_and_overgroup d earlier hq chosen
    structural alternatives F hne hcenterless action overgroup
  exact recognition G ⟨z, V, hz⟩
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
