module

public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.FaithfulSeed
public import CFSG.Quasithin.Chapter14.Section03.Prelim.FaithfulSource.Contract
public import CFSG.Quasithin.ChapterA.Section04.ReducedWitness.Centralizing
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.SourceKnownSimple

/-!
# Faithful-component membership in the 14.3.25 contrary branch

The H-orbit of Z(LT) ∩ U is a reduced module for the actual H. A component
of H outside N_G(L) must move this module: its centralizer lies in the
normalizer of the seed, which is contained in the unique maximal two-local
overgroup N_G(L). The intrinsic-module criterion then places the component
in the genuine faithful local family, so the earlier faithful classifier
applies to the original component and its literal two-core quotient.

The remaining work in 14.3.25 is to use the source model alternatives to
exclude the nonsolvable and solvable cases. This module proves the
faithful-family entry step only. The earlier faithful classifier is assembled
in Chapter14/Section03/Prelim/FaithfulSource/Classification.lean; its remaining
source inputs are discharged by the outer source assembly.

Source: Aschbacher--Smith, 14.3.25, printed p.1001; 14.3.4.1 and 1.2.10.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterA.Section04
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem reduced_moved_component_faithful
    (hE : IsEvenCharacteristicAt T) {A C W : Subgroup G}
    (hA : A ∈ Chapter1.HOver G (T : Set G))
    (hC : C ∈ Chapter1.cComponentsIn A)
    (hWA : W ≤ A) (hr : IsPReduced 2 (W.subgroupOf A))
    (hm : ⁅W,C⁆ ≠ ⊥) : C ∈ MainForward.faithfulLocalComponents T := by
  have hlocal := ((Chapter1.lemma_1_2_6 T hA).1 hC).2
  have hp := Chapter1.Section02.Adequate.mem_L_isPPerfect hlocal
  let e := subgroupOfEquivOfLe hC.1
  have hp' : IsPPerfect 2 (C.subgroupOf A) := hp.of_surjective
    e.symm.toMonoidHom e.symm.surjective
  have hle := (commutator_mono hr.le_reducedPSubgroup (le_refl (C.subgroupOf A))).trans
    (reduced_commutator_le_intrinsicModule _ hC.2.subnormal hp')
  have hmapped := map_mono (f := A.subtype) hle
  rw [map_commutator, map_subgroupOf_eq_of_le hWA, map_subgroupOf_eq_of_le hC.1,
    ← intrinsicSignalizerModule_map_of_injective A.subtype A.subtype_injective,
    map_subgroupOf_eq_of_le hC.1] at hmapped
  apply (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff_module T hE).mpr
  exact ⟨hlocal, fun he => hm (le_bot_iff.mp (he ▸ hmapped))⟩

omit [Finite G] in
private theorem pointNormalizer_mem_HOver (F : InvariantFlag T V 3)
    [IsElementaryAbelian 2 V] : F.H ∈ Chapter1.HOver G (T : Set G) := by
  let : IsElementaryAbelian 2 (F.Vi 1) := IsElementaryAbelian.of_le (F.le_seed 1)
  have hp : F.Vi 1 ≤ F.H.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 (F.Vi 1))
    ((F.le_seed 1).trans ((le_conjugateSpanBy V F.H).trans F.U_le_H)) le_rfl
  refine ⟨?_, F.invariant 1⟩
  intro he
  have hz : F.Vi 1 = ⊥ := le_bot_iff.mp (he ▸ hp)
  have hc := F.card 1 (by decide)
  rw [hz, card_bot] at hc
  norm_num at hc

theorem source_faithful_test_centralizer (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hz : centralLTSeed F L ≠ ⊥) :
    centralizer (faithfulTestModule F L : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨hs, _, hn⟩ := source_centralLT_seed d earlier hq chosen structural alternatives F
  have hlocal : IsTwoLocal (normalizer (centralLTSeed F L : Set G)) :=
    ⟨centralLTSeed F L, hz, hs.isPGroup, rfl⟩
  obtain ⟨R, hNR, hR⟩ := Finite.exists_le_maximal hlocal
  have unique : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S A hA
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hA
  have hm := (higherRankHypothesis d earlier hq chosen).maximal_unique structural unique
  have he : R = normalizer (L : Set G) := by
    have hmem : R ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N} :=
      ⟨hR, hn.trans hNR⟩
    rw [hm.2, Set.mem_singleton_iff] at hmem
    exact hmem
  exact (centralizer_le (le_conjugateSpanBy (centralLTSeed F L) F.H)).trans
    ((Subgroup.centralizer_le_normalizer _).trans (he ▸ hNR))

theorem source_faithful_component (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hz : centralLTSeed F L ≠ ⊥)
    {C : Subgroup G} (hC : C ∈ Chapter1.cComponentsIn F.H)
    (hout : ¬ C ≤ normalizer (L : Set G)) :
    C ∈ MainForward.faithfulLocalComponents T := by
  let := chosen.elementary
  obtain ⟨hW, hr⟩ := source_faithful_test_reduced d earlier hq chosen structural alternatives F
  have hm : ⁅faithfulTestModule F L, C⁆ ≠ ⊥ := by
    intro he
    rw [commutator_comm] at he
    exact hout ((commutator_eq_bot_iff_le_centralizer.mp he).trans
      (source_faithful_test_centralizer d earlier hq chosen structural alternatives F hz))
  exact reduced_moved_component_faithful (d.qtke.evenCharacteristic T)
    (pointNormalizer_mem_HOver F) hC
    (hW.trans ((map_subtype_le (center F.U)).trans F.U_le_H)) hr hm

theorem source_faithful_component_classification (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) (hz : centralLTSeed F L ≠ ⊥)
    {C : Subgroup G} (hC : C ∈ Chapter1.cComponentsIn F.H)
    (hout : ¬ C ≤ normalizer (L : Set G)) :
    (Nonempty ((C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5)) ∨
      Nonempty ((C ⧸ pCore 2 C) ≃* Matrix.PSL3Two.PSL)) ∧
      (C.subgroupOf (C ⊔ (T : Subgroup G))).Normal ∧ C ∈ Chapter1.LStar G T := by
  have hf := source_faithful_component d earlier hq chosen structural alternatives F hz hC hout
  have hh := (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T C).mp hf
  exact classification C hh.1 hh.2

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
