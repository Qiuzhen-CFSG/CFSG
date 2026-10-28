module
public import CFSG.Quasithin.ChapterA.Section04.ReducedWitness.Intrinsic
public import CFSG.Quasithin.Chapter1.Section02.Adequate.Families
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.SelfCentralizingCoreInheritance
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.NaturalSetup
/-!
# The actual faithful component from omega-center movement

A subnormal two-perfect subgroup acts on the ambient two-core through
its own two-core. A.4.8 therefore puts the resulting omega-center
commutator in its intrinsic module. Nontrivial movement makes that
module nontrivial. Subnormal characteristic-two inheritance and the
actual ambient Sylow then give membership in the faithful local family.

The final natural-source application derives the point group's local
and characteristic-two hypotheses from the original QTKE configuration.
It retains only the selected C-component and reduction (a)'s omega-center
containment and movement. No universal A.4.9 premise is used.
Source: Aschbacher–Smith, 13.3.14(e), printed p.892.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]
theorem subnormal_intrinsicModule_ne_bot_of_omega_movement
    (K U : Subgroup G) (hK : K.IsSubnormal) (hp : IsPPerfect 2 K)
    (hU : U ≤ omegaOneCenterAmbient (pCore 2 G)) (hm : ⁅U,K⁆ ≠ ⊥) :
    intrinsicSignalizerModule K ≠ ⊥ := by
  have hn : K ≤ normalizer (pCore 2 G : Set G) := le_normalizer_of_normal
  have hc : ⁅K,pCore 2 G⁆ ≤ K.pCoreIn 2 := by
    rw [commutator_comm]
    exact (commutator_le_core_commutator_of_isSubnormal K (pCore 2 G)
      hK hp pCore_isPGroup hn).trans (map_mono (commutator_le_left _ _))
  have hi := signalizerModule_le_intrinsicModule K (pCore 2 G) hp hn
    (pCoreIn_le_of_subnormal 2 hK) hc
  rw [signalizerModule_eq_commutator_omegaCenter, commutator_comm K] at hi
  intro he
  exact hm (le_bot_iff.mp ((commutator_mono hU le_rfl).trans (hi.trans_eq he)))

theorem source_component_faithful_local
    (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (hH : H ∈ Chapter1.H G)
    (hHe : H ∈ Chapter1.He G)
    (K U : Subgroup H) (hK : K.IsCComponent)
    (hU : U ≤ omegaOneCenterAmbient (pCore 2 H)) (hm : ⁅U,K⁆ ≠ ⊥) :
    K.map H.subtype ∈ Chapter1.L G (T : Subgroup G) ∧
      IsFaithfulSignalizerType (K.map H.subtype) := by
  let B := K.map H.subtype
  have hBH : B ≤ H := map_subtype_le _
  have hcomp : (B.subgroupOf H).IsCComponent := by
    change ((K.map H.subtype).comap H.subtype).IsCComponent
    rwa [comap_map_eq_self_of_injective H.subtype_injective]
  have hB : B ∈ Chapter1.L G (T : Subgroup G) :=
    Chapter1.mem_L_of_cComponent hH
      ⟨T.subtype hTH, by simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH]⟩ hBH hcomp
  have hpB := Chapter1.Section02.Adequate.mem_L_isPPerfect hB
  have hpK : IsPPerfect 2 K := hpB.of_surjective
    (K.equivMapOfInjective H.subtype H.subtype_injective).symm.toMonoidHom
    (K.equivMapOfInjective H.subtype H.subtype_injective).symm.surjective
  have hmK := subnormal_intrinsicModule_ne_bot_of_omega_movement K U hK.subnormal hpK hU hm
  have hmB : intrinsicSignalizerModule B ≠ ⊥ := by
    change intrinsicSignalizerModule (K.map H.subtype) ≠ ⊥
    rw [intrinsicSignalizerModule_map_of_injective H.subtype H.subtype_injective]
    exact fun hz => hmK ((map_eq_bot_iff_of_injective _ H.subtype_injective).mp hz)
  have hne : B ≠ ⊥ := fun hz => hK.ne_bot
    ((map_eq_bot_iff_of_injective _ H.subtype_injective).mp hz)
  have hchar : centralizer (pCore 2 B : Set B) ≤ pCore 2 B :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2
      (K.equivMapOfInjective H.subtype H.subtype_injective)).mp
      (subnormal_core_selfCentralizing (Chapter1.mem_He_iff.mp hHe) K hK.subnormal)
  exact ⟨hB, ⟨⟨hne,hpB,generalizedFitting_eq_pCore_of_selfCentralizing 2 hchar⟩,hmB⟩⟩

theorem natural_source_component_faithful
    {T : Sylow 2 G} {L V P E U M H : Subgroup G}
    (d : Section08.SourceCompletion.NaturalSetup T L V P E U M H)
    (K : Subgroup H) (hK : K.IsCComponent)
    (ha : U ≤ omegaOneCenterAmbient (H.pCoreIn 2))
    (hm : ⁅U,K.map H.subtype⁆ ≠ ⊥) :
    K.map H.subtype ∈ Chapter1.L G (T : Subgroup G) ∧
      IsFaithfulSignalizerType (K.map H.subtype) := by
  have hTH : (T : Subgroup G) ≤ H := d.first_normalizer ▸ d.line_stable
  have hne : P ≠ ⊥ := by intro he; have hc := d.line_card; simp [he] at hc
  have htwo : IsTwoLocal H := by
    rw [d.first_normalizer]
    exact ⟨P,hne,IsPGroup.of_card (n := 1) (by simpa using d.line_card),rfl⟩
  have hH := Chapter1.mem_H_of_isTwoLocal htwo
  have hHe := Chapter1.twoLocal_mem_He_of_sylow_le T
    (d.counterexample.qtke.toIsQTKE.evenCharacteristic T) htwo hTH
  have hω : (omegaOneCenterAmbient (pCore 2 H)).map H.subtype =
      omegaOneCenterAmbient (H.pCoreIn 2) :=
    (omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective _).symm
  have hUH : U ≤ H := ha.trans (hω ▸ map_subtype_le _)
  have hUi : U.subgroupOf H ≤ omegaOneCenterAmbient (pCore 2 H) := by
    intro u hu
    have hh := ha hu
    rw [← hω] at hh
    obtain ⟨v,hv,he⟩ := hh
    exact (H.subtype_injective he) ▸ hv
  have hmi : ⁅U.subgroupOf H,K⁆ ≠ ⊥ := by
    intro he
    have hh := congrArg (fun A : Subgroup H => A.map H.subtype) he
    rw [map_commutator,map_subgroupOf_eq_of_le hUH,Subgroup.map_bot] at hh
    exact hm hh
  exact source_component_faithful_local T H hTH hH hHe K _ hK hUi hmi
end CFSG.Quasithin.Chapter13.Section03.Noncentrality
