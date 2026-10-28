module

public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup.Consumer
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup.Source

/-!
# Conditional assembly of the original nonextraspecial HS configuration

The two independent source steps are 14.3.31--32 (`LocalStructure`) and
14.3.33 (`OvergroupStructure`). From them the original flag supplies the
involution and elementary subgroup required in I.4.8. Even characteristic
identifies both generalized Fitting subgroups with their two-cores. Transport
of the actual central product and the natural action supplies HS1, while
the literal equality N_G(V)=L supplies HS2 and its original L/O₂(L) quotient.

The original overgroup structure is constructed in `Overgroup.Source`.
The guarded local source and its full type-HS application are connected
in `Overgroup.SourceAt`, above this umbrella. The recognition theorem
I.4.8 remains an explicit independent input, so this module does not claim
a proof of 14.3.26. Final 14.4.14 assembly remains with qt-d-14414-source.

Source: Aschbacher--Smith, printed p.1005, final paragraph of 14.3, and the
exact type-HS definition and I.4.8 on printed p.418.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Construct precisely HS1--HS2 on the original seed and point centralizer.
The generalized Fitting and relative-core transports are proved here. -/
theorem type_of_local_and_overgroup (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (localData : LocalStructure L F)
    (overgroup : OvergroupStructure L F) :
    ∃ z : G, F.Vi 1 = zpowers z ∧ HigmanSims.TypeAt z V := by
  let := chosen.elementary
  obtain ⟨z, hz, hpoint, hH⟩ := source_point_centralizer F
  have hfit := source_fitting d earlier hq chosen alternatives F
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

/-- The actual source consumer of I.4.8. Its three independent intermediate
premises remain explicit until their producers have completed their proofs. -/
theorem recognition_of_local_and_overgroup (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (localData : LocalStructure L F)
    (overgroup : OvergroupStructure L F) (recognition : HigmanSims.Recognition.{u}) :
    Nonempty (G ≃* Sporadic.LeechRelated.HS.Carrier) := by
  obtain ⟨z, _, hz⟩ := type_of_local_and_overgroup d earlier hq chosen alternatives
    F localData overgroup
  exact recognition G ⟨z, V, hz⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
