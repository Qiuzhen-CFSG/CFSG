module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.At.CenterlessPreparation
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.At.Normalizers

/-!
# The faithful test module and original component at G,T

The actual central LT seed misses the point and is elementary abelian.
Its H-orbit lies in Z(U) and is reduced. Maximal-local uniqueness at G,T
places its centralizer inside N_G(L), so every relative component of H
outside that normalizer moves the test module. The intrinsic-module
criterion then puts that same component in the faithful local family.
The genuine earlier classifier consequently applies to its literal
quotient by O₂(C), with its relative normality retained.

These are the initial faithful-family steps of 14.3.25. They do not
assert the later seed exclusion or centerlessness; their construction
at the local earlier-source boundary continues in this task.
Source: Aschbacher--Smith 14.3.25, p.1001, and 1.2.10,14.3.4(1).
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterA.Section04
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_point_inf_centerLT_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) :
    F.Vi 1 ⊓ Chapter12.Section08.centerIn (L ⊔ (T : Subgroup G)) = ⊥ := by
  let := chosen.elementary
  obtain ⟨g, hgP, hgH⟩ := source_conjugator_at d earlier hq chosen structural F
  apply le_bot_iff.mp
  rintro x ⟨hp, hxZ⟩
  change x = 1
  by_contra hx
  have ho : orderOf x = 2 := orderOf_eq_prime_iff.mpr
    ⟨elemPow_eq_one_of_isElementaryAbelian x (F.le_seed 1 hp), hx⟩
  have he : zpowers x = F.Vi 1 := eq_of_le_of_card_ge (zpowers_le.mpr hp) (by
    rw [Nat.card_zpowers, ho]
    simpa using (F.card 1 (by decide)).le)
  have hgc : g ∈ centralizer ({x} : Set G) :=
    mem_centralizer_singleton_iff.mpr (Chapter12.Section08.centerIn_le_centralizer _ hxZ g hgP.1)
  have hgc' : g ∈ centralizer (zpowers x : Set G) := by
    simpa only [zpowers_eq_closure, centralizer_closure] using hgc
  apply hgH
  change g ∈ normalizer (F.Vi 1 : Set G)
  rw [← he]
  exact Subgroup.centralizer_le_normalizer _ hgc'

theorem source_centralLT_seed_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) :
    IsElementaryAbelian 2 (centralLTSeed F L) ∧ centralLTSeed F L ≤ F.ZU ∧
      L ⊔ (T : Subgroup G) ≤ normalizer (centralLTSeed F L : Set G) := by
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  let := chosen.elementary
  have hUT := source_closure_le_sylow_at d earlier hq chosen structural alternatives F
  have hZC : centralLTSeed F L ≤ centralizer ((L ⊔ (T : Subgroup G) : Subgroup G) : Set G) := by
    intro x hx y hy
    exact Chapter12.Section08.centerIn_le_centralizer _ hx.1 y hy
  let : IsMulCommutative (centralLTSeed F L) := le_centralizer_iff_isMulCommutative.mp
    (hZC.trans (centralizer_le (inf_le_right.trans (hUT.trans le_sup_right))))
  obtain ⟨_, hsquare⟩ := F.localKernel_commutator_squares d.qtke L
    (normalizer (L : Set G)) (by decide) chosen.le_sylow chosen.normalizes
    (h.sylow_normalizes_at structural) h.residual (fun _ => ⟨h.naturalMarking⟩)
    (h.flag_escape_at F alternatives)
  have hs : IsElementaryAbelian 2 (centralLTSeed F L) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => by
      apply Subtype.ext
      have hm : (x : G) ^ 2 ∈ F.Vi 1 ⊓
          Chapter12.Section08.centerIn (L ⊔ (T : Subgroup G)) :=
        ⟨hsquare x x.property.2, pow_mem x.property.1 2⟩
      rwa [source_point_inf_centerLT_at d earlier hq chosen structural F, mem_bot] at hm }
  have hZU : centralLTSeed F L ≤ F.ZU := by
    intro x hx
    refine ⟨⟨x, hx.2⟩, mem_center_iff.mpr ?_, rfl⟩
    intro y
    exact Subtype.ext (hZC hx y (mem_sup_right (hUT y.property)))
  exact ⟨hs, hZU, (le_centralizer_iff.mp hZC).trans (Subgroup.centralizer_le_normalizer _)⟩

theorem source_faithful_test_reduced_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) :
    faithfulTestModule F L ≤ F.ZU ∧
      IsPReduced 2 ((faithfulTestModule F L).subgroupOf F.H) := by
  obtain ⟨hs, hZ, _⟩ := source_centralLT_seed_at d earlier hq chosen structural alternatives F
  let := hs
  have hUT := source_closure_le_sylow_at d earlier hq chosen structural alternatives F
  have hZC : centralLTSeed F L ≤ centralizer (T : Set G) := by
    intro x hx t ht
    exact Chapter12.Section08.centerIn_le_centralizer _ hx.1 t (mem_sup_right ht)
  refine ⟨conjugateSpanBy_le hZ ((le_normalizer_conjugateSpanBy V F.H).trans
    (normalizer_le_normalizer_characteristic_image F.U (center F.U))), ?_⟩
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  exact reduced_conjugateSpan_of_sylow_central T F.H (centralLTSeed F L)
    (F.invariant 1) (inf_le_right.trans hUT) hZC
    (F.localKernel_characteristicTwo d.qtke L (normalizer (L : Set G)) F.H
      (h.point_mem_Hz_at F alternatives))

theorem source_faithful_test_centralizer_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hz : centralLTSeed F L ≠ ⊥) :
    centralizer (faithfulTestModule F L : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨hs, _, hn⟩ := source_centralLT_seed_at d earlier hq chosen structural alternatives F
  have hlocal : IsTwoLocal (normalizer (centralLTSeed F L : Set G)) :=
    ⟨centralLTSeed F L, hz, hs.isPGroup, rfl⟩
  obtain ⟨R, hNR, hR⟩ := Finite.exists_le_maximal hlocal
  have hm := Chapter14.Section03.CaseOneSource.source_normalizers_at
    d earlier hq chosen structural
  have he : R = normalizer (L : Set G) := by
    have hmem : R ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N} :=
      ⟨hR, hn.trans hNR⟩
    rw [hm.2.2.2.1, Set.mem_singleton_iff] at hmem
    exact hmem
  exact (centralizer_le (le_conjugateSpanBy (centralLTSeed F L) F.H)).trans
    ((Subgroup.centralizer_le_normalizer _).trans (he ▸ hNR))

theorem source_faithful_component_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hz : centralLTSeed F L ≠ ⊥)
    {C : Subgroup G} (hC : C ∈ Chapter1.cComponentsIn F.H)
    (hout : ¬ C ≤ normalizer (L : Set G)) :
    C ∈ MainForward.faithfulLocalComponents T := by
  let := chosen.elementary
  obtain ⟨hW, hr⟩ := source_faithful_test_reduced_at d earlier hq chosen structural alternatives F
  have hm : ⁅faithfulTestModule F L, C⁆ ≠ ⊥ := by
    intro he
    rw [commutator_comm] at he
    exact hout ((commutator_eq_bot_iff_le_centralizer.mp he).trans
      (source_faithful_test_centralizer_at d earlier hq chosen structural alternatives F hz))
  have hH : F.H ∈ Chapter1.HOver G (T : Set G) := by
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
  have hlocal := ((Chapter1.lemma_1_2_6 T hH).1 hC).2
  have hp := Chapter1.Section02.Adequate.mem_L_isPPerfect hlocal
  let e := subgroupOfEquivOfLe hC.1
  have hp' : IsPPerfect 2 (C.subgroupOf F.H) := hp.of_surjective
    e.symm.toMonoidHom e.symm.surjective
  have hle := (commutator_mono hr.le_reducedPSubgroup (le_refl (C.subgroupOf F.H))).trans
    (reduced_commutator_le_intrinsicModule _ hC.2.subnormal hp')
  have hmapped := map_mono (f := F.H.subtype) hle
  rw [map_commutator,
    map_subgroupOf_eq_of_le (hW.trans ((map_subtype_le (center F.U)).trans F.U_le_H)),
    map_subgroupOf_eq_of_le hC.1,
    ← intrinsicSignalizerModule_map_of_injective F.H.subtype F.H.subtype_injective,
    map_subgroupOf_eq_of_le hC.1] at hmapped
  apply (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff_module T
    (d.qtke.evenCharacteristic T)).mpr
  exact ⟨hlocal, fun he => hm (le_bot_iff.mp (he ▸ hmapped))⟩

theorem source_faithful_component_classification_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) (hz : centralLTSeed F L ≠ ⊥)
    {C : Subgroup G} (hC : C ∈ Chapter1.cComponentsIn F.H)
    (hout : ¬ C ≤ normalizer (L : Set G)) :
    (Nonempty ((C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5)) ∨
      Nonempty ((C ⧸ pCore 2 C) ≃* Matrix.PSL3Two.PSL)) ∧
      (C.subgroupOf (C ⊔ (T : Subgroup G))).Normal ∧ C ∈ Chapter1.LStar G T := by
  have hf := source_faithful_component_at d earlier hq chosen structural alternatives F hz hC hout
  have hh := (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T C).mp hf
  exact classification C hh.1 hh.2

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
