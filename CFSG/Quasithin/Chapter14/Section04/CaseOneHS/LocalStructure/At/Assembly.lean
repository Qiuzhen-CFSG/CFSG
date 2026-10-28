module

public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.At.Geometry

/-!
# The literal HS application from earlier inputs at G,T

The local closure theorem supplies the two-group and Frattini inputs to the
existing embedded central-product construction. The point-centralizer and
normalizer cores then transport LocalStructure and OvergroupStructure to
HS1--HS2 on the original point and seed, and hence to the actual HS carrier.

Centerlessness and the action are still explicit in the local construction;
this file does not claim to localize their completed universal source proofs.
Overgroup transfer and I.4.8 recognition remain with qt-d-14414-hs-source.
The earlier-source producers must supply their genuine implications at this
G,T; no local statement is promoted to a universal one.
Source: Aschbacher--Smith 14.3.31--33 and I.4.8,
printed pp.1002--1005 and 418.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Construct all LocalStructure fields using the original local closure. -/
theorem localStructure_of_centerless_action_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hcenterless : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (action : ActionStructure F) :
    LocalStructure L F := by
  obtain ⟨hp, hphi, _⟩ :=
    source_closure_at d earlier hq chosen structural alternatives F hne
  exact {
    centerless := hcenterless
    core_shape := action.coreShape F hp hphi
    natural := action.natural
    kernel := action.natural.kernel F
    component := action.component }

/-- Supply HS1--HS2 on the literal original point and seed. -/
theorem type_of_local_and_overgroup_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (localData : LocalStructure L F)
    (overgroup : OvergroupStructure L F) :
    ∃ z : G, F.Vi 1 = zpowers z ∧ HigmanSims.TypeAt z V := by
  let := chosen.elementary
  obtain ⟨z, hz, hpoint, hH⟩ := source_point_centralizer F
  have hfit := source_fitting_at d earlier hq chosen alternatives F
  have hfitM := source_normalizer_fitting d chosen F
  let e : F.U ≃* pCore 2 F.H :=
    (MulEquiv.subgroupCongr overgroup.closure_core).trans
      ((pCore 2 F.H).equivMapOfInjective F.H.subtype F.H.subtype_injective).symm
  refine ⟨z, hpoint, {
    involution := hz
    elementary := chosen.elementary
    seed_card := by simpa [F.last] using F.card 3 (by decide)
    centralizer_core := ?_
    centralizer_quotient := ?_
    seed_le_core := ?_
    normalizer_core := ?_
    normalizer_quotient := ?_ }⟩
  · change HigmanSims.CoreShape (generalizedFitting (centralizer ({z} : Set G)))
    rw [← hH, hfit]
    exact localData.core_shape.of_equiv e
  · change Nonempty
      ((centralizer ({z} : Set G) ⧸ generalizedFitting (centralizer ({z} : Set G))) ≃*
        Equiv.Perm (Fin 5))
    rw [← hH]
    obtain ⟨q⟩ := localData.quotient F
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hfit).trans q⟩
  · change V ≤ (generalizedFitting (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype
    rw [← hH, hfit]
    change V ≤ F.H.pCoreIn 2
    rw [← overgroup.closure_core]
    exact le_conjugateSpanBy V F.H
  · rw [hfitM, overgroup.seed_normalizer]
    exact overgroup.homocyclic
  · apply ClassicalGroup.IsPSL.of_mulEquiv _
      (QuotientGroup.quotientMulEquivOfEq hfitM)
    rw [overgroup.seed_normalizer]
    exact hq

/-- Apply I.4.8 to this actual local configuration. -/
theorem recognition_of_local_and_overgroup_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (localData : LocalStructure L F)
    (overgroup : OvergroupStructure L F) (recognition : HigmanSims.Recognition.{u}) :
    Nonempty (G ≃* Sporadic.LeechRelated.HS.Carrier) := by
  obtain ⟨z, _, hz⟩ := type_of_local_and_overgroup_at d earlier hq chosen alternatives
    F localData overgroup
  exact recognition G ⟨z, V, hz⟩

/-- The local construction is applied to the original type-HS consumer.
Only the two source conclusions still awaiting localization remain here. -/
theorem type_of_centerless_action_and_overgroup_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hcenterless : Chapter12.Section08.centerIn (F.I₂ L) = ⊥) (action : ActionStructure F)
    (overgroup : OvergroupStructure L F) :
    ∃ z : G, F.Vi 1 = zpowers z ∧ HigmanSims.TypeAt z V :=
  type_of_local_and_overgroup_at d earlier hq chosen alternatives F
    (localStructure_of_centerless_action_at d earlier hq chosen structural alternatives
      F hne hcenterless action) overgroup

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
