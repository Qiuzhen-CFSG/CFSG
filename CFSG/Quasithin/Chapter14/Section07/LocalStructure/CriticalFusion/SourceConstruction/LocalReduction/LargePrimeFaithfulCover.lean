module
public import CFSG.Quasithin.Chapter14.Section03.Prelim.FaithfulSource.SylowTransport
public import CFSG.Quasithin.ChapterA.Section04.ReducedWitness.Centralizing
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.SourceKnownSimple
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeComponentCover

/-!
# The faithful common-space component and its full normalizer

When N_G(C) contains an ambient Sylow S, its normal elementary eight-group
C is reduced: the literal action quotient is GL₃(2), with trivial two-core.
The component covering that action moves C, so the reduced commutator detects
its nonzero intrinsic signalizer module. It therefore belongs to L_f(G,S).

Transport earlier 14.3.4 from the original Sylow to S. It makes the same
component maximal and gives a simple quotient by its intrinsic two-core.
Hence its solvable radical equals that core, and the previously identified
full action kernel does too. The resulting quotient is actually L₃(2),
excluding the natural E₄₉ extension in this ambient Sylow branch. The proved
1.2.7 then makes the component normalizer the unique maximal two-local
overgroup of its join with S. The source application uses the original T_A.

Source: Aschbacher–Smith 14.7.6, printed p.1045, using 14.3.4 and 1.2.7;
refs/quasithin.pdf. The five-core contradiction is not asserted here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open ChapterA.Section04 Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem common_eight_reduced
    (C : Subgroup G) [IsElementaryAbelian 2 C] (hc : Nat.card C = 8)
    (hfull : Function.Surjective C.normalizerMonoidHom) :
    IsPReduced 2 (C.subgroupOf (normalizer (C : Set G))) := by
  let N := normalizer (C : Set G)
  let U := C.subgroupOf N
  let : U.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  have hk : C.normalizerMonoidHom.ker = centralizer (U : Set N) := by
    apply map_injective N.subtype_injective
    rw [normalizerMonoidHom_ker,map_subgroupOf_eq_of_le (Subgroup.centralizer_le_normalizer _),
      map_centralizer_subtype,map_subgroupOf_eq_of_le C.le_normalizer,
      inf_eq_right.mpr (Subgroup.centralizer_le_normalizer _)]
  let e := QuotientGroup.liftEquiv (centralizer (U : Set N)) hfull hk.symm
  obtain ⟨a⟩ := MulAut.elementaryEight_equiv_PSL3 hc
  refine ⟨inferInstance,IsElementaryAbelian.subgroupOf C.le_normalizer,?_⟩
  have hh := pCore_map_iso 2 (e.trans a)
  rw [Matrix.PSL3Two.pCore_two_PSL_eq_bot] at hh
  exact ((pCore 2 (N ⧸ centralizer (U : Set N))).map_eq_bot_iff_of_injective
    (e.trans a).injective).mp hh

/-- The component covering the common eight-group has nonzero intrinsic
module and lies in the actual faithful family at the supplied ambient Sylow. -/
theorem common_eight_component_faithful
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (C : Subgroup G) [IsElementaryAbelian 2 C] (hc : Nat.card C = 8)
    (S : Sylow 2 G) (hS : (S : Subgroup G) ≤ normalizer (C : Set G))
    (D : Subgroup (normalizer (C : Set G))) (hD : D.IsCComponent)
    (hm : D.map C.normalizerMonoidHom = ⊤) :
    D.map (normalizer (C : Set G)).subtype ∈ Chapter1.L G (S : Subgroup G) ∧
      IsFaithfulSignalizerType (D.map (normalizer (C : Set G)).subtype) := by
  let N := normalizer (C : Set G)
  let DA := D.map N.subtype
  have hcore : C ≤ N.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 C) C.le_normalizer le_rfl
  have hN : N ∈ Chapter1.H G := by
    intro he
    have hb : C = ⊥ := le_bot_iff.mp (he ▸ hcore)
    rw [hb,card_bot] at hc
    omega
  have hDN : DA.subgroupOf N = D := comap_map_eq_self_of_injective N.subtype_injective D
  have hDL : DA ∈ Chapter1.L G (S : Subgroup G) :=
    Chapter1.mem_L_of_cComponent hN
      ⟨S.subtype hS,by
        change ((S : Subgroup G).subgroupOf N).map N.subtype = (S : Subgroup G)
        exact map_subgroupOf_eq_of_le hS⟩
      (map_subtype_le D) (hDN.symm ▸ hD)
  have hf : Function.Surjective C.normalizerMonoidHom := by
    intro a
    obtain ⟨d,hd,rfl⟩ := hm.ge (mem_top a)
    exact ⟨d,rfl⟩
  have hred := common_eight_reduced C hc hf
  have hp : IsPPerfect 2 D :=
    (Chapter1.Section02.Adequate.mem_L_isPPerfect hDL).of_surjective
      (D.equivMapOfInjective N.subtype N.subtype_injective).symm.toMonoidHom
      (D.equivMapOfInjective N.subtype N.subtype_injective).symm.surjective
  have hmod : intrinsicSignalizerModule D ≠ ⊥ := by
    intro hz
    have hmoved : ⁅C.subgroupOf N,D⁆ = ⊥ := bot_unique
      ((commutator_mono hred.le_reducedPSubgroup le_rfl).trans
        ((reduced_commutator_le_intrinsicModule D hD.subnormal hp).trans hz.le))
    have hcentral := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hmoved)
    have hker : D ≤ C.normalizerMonoidHom.ker := by
      rw [normalizerMonoidHom_ker]
      intro d hd c hc
      exact congrArg Subtype.val (hcentral hd ⟨c,C.le_normalizer hc⟩ hc)
    have him : D.map C.normalizerMonoidHom = ⊥ :=
      (Subgroup.map_eq_bot_iff D).mpr hker
    rw [hm] at him
    have hcard := card_mulAut_of_elementary_eight C hc
    have h1 : Nat.card (MulAut C) = 1 := by
      rw [←card_top (G := MulAut C),him,card_bot]
    omega
  refine ⟨hDL,Chapter1.Section02.Adequate.mem_L_isSignalizerType S (hG.evenCharacteristic S) hDL,?_⟩
  rw [intrinsicSignalizerModule_map_of_injective N.subtype N.subtype_injective]
  exact fun hz => hmod (((intrinsicSignalizerModule D).map_eq_bot_iff_of_injective
    N.subtype_injective).mp hz)

/-- Earlier 14.3.4 at the original Sylow makes the full covering component
maximal at the new Sylow, identifies its entire action kernel with its two-core,
and supplies the unique maximal two-local overgroup of their join. -/
theorem common_eight_component_faithful_normalizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (C : Subgroup G) [IsElementaryAbelian 2 C] (hc : Nat.card C = 8)
    (S : Sylow 2 G) (hS : (S : Subgroup G) ≤ normalizer (C : Set G))
    (D : Subgroup (normalizer (C : Set G))) (hD : D.IsCComponent)
    (hm : D.map C.normalizerMonoidHom = ⊤) :
    let DA := D.map (normalizer (C : Set G)).subtype
    DA ∈ Chapter1.LStar G (S : Subgroup G) ∧ IsFaithfulSignalizerType DA ∧
      (DA.subgroupOf (DA ⊔ (S : Subgroup G))).Normal ∧
      (C.normalizerMonoidHom.comp D.subtype).ker = pCore 2 D ∧
      Nonempty ((D ⧸ pCore 2 D) ≃* Matrix.PSL3Two.PSL) ∧
      normalizer (C : Set G) ≤ normalizer (DA : Set G) ∧
      IsMaximalTwoLocal (normalizer (DA : Set G)) ∧
      (∀ M : Subgroup G, IsMaximalTwoLocal M → DA ⊔ (S : Subgroup G) ≤ M →
        M = normalizer (DA : Set G)) := by
  let N := normalizer (C : Set G)
  let DA := D.map N.subtype
  obtain ⟨hDL,hDf⟩ := common_eight_component_faithful hG C hc S hS D hD hm
  obtain ⟨hmodel,hn,hmax⟩ := (faithful.sylow_transport hG T S) DA hDL hDf
  let : IsSimpleGroup (DA ⧸ pCore 2 DA) := by
    rcases hmodel with he | he
    · let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
      exact he.some.isSimpleGroup
    · let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
      exact he.some.isSimpleGroup
  let eD := D.equivMapOfInjective N.subtype N.subtype_injective
  let eQ := QuotientGroup.congr (pCore 2 D) (pCore 2 DA) eD (pCore_map_iso 2 eD)
  let : IsSimpleGroup (D ⧸ pCore 2 D) := eQ.isSimpleGroup
  let := hD.perfect
  have hrad : solvableRadical D = pCore 2 D := PerfectCoreTwoExtension.radical_eq_core
  obtain ⟨hnD,hker,_⟩ := common_eight_component_full_cover hG C hc D hD hm
  rw [hrad] at hker
  have hsur : Function.Surjective (C.normalizerMonoidHom.comp D.subtype) := by
    intro a
    obtain ⟨d,hd,hda⟩ := hm.ge (mem_top a)
    exact ⟨⟨d,hd⟩,hda⟩
  obtain ⟨a⟩ := MulAut.elementaryEight_equiv_PSL3 hc
  have he : Nonempty ((D ⧸ pCore 2 D) ≃* Matrix.PSL3Two.PSL) :=
    ⟨(QuotientGroup.liftEquiv (pCore 2 D) hsur hker.symm).trans a⟩
  let := hnD
  have hND : N ≤ normalizer (DA : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      D.le_normalizer_map N.subtype
  have horbit : componentOrbit DA (S : Subgroup G) = DA := le_antisymm
    (iSup_conjugates_le_of_le_normalizer DA (S : Subgroup G) DA le_rfl (hS.trans hND))
    (le_componentOrbit DA _)
  have hu := Chapter1.Section02.nonsolvable_uniqueness_knownSimple hG S hmax
  refine ⟨hmax,hDf,hn,hker,he,hND,?_,?_⟩
  · simpa only [horbit] using hu.normalizer_maximal
  · intro M hM hDSM
    simpa only [horbit] using hu.normalizer_unique M hM hDSM

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
