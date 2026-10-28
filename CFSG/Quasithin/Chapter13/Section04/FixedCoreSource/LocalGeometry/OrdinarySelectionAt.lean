module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.ComponentGeometry
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentSeedSource
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.OrdinaryOutsideAt
public import Theory.GroupTheory.TwoThreeSolvable

/-!
# An escaping component before the ordinary normalizer supplement

Apply the full-normalizer version of 13.3.8 to the Sylow orbit of an
actual C-component in the escaping vector centralizer. That orbit is
perfect, so its {2,3}-group conclusion would contradict nonsolvability.
The fixed line then proves faithful-locality, and the guarded 13.3.2
input gives relative normality and maximality of the same selected core.

All structural uses occur at the original G,T. In particular M=LT and
a supplied outside-subgroup callback are absent. The later supplement
argument still needs the corresponding source control at the selected K.
Source: Aschbacher--Smith 13.3.8 and 13.4.5--6, pp.886--887,898.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Nonsolvable
open Section03.Noncentrality.SupercriticalSource Chapter1.Section02.Adequate
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

private theorem relative_component_escape_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    {z : G} (hzT : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (hout : ¬ centralizer ({z} : Set G) ≤ normalizer (L : Set G))
    (K : Subgroup (centralizer ({z} : Set G))) (hK : K.IsCComponent) :
    ¬ K.map (centralizer ({z} : Set G)).subtype ≤ normalizer (L : Set G) := by
  let H := centralizer ({z} : Set G)
  have hTH : (T : Subgroup G) ≤ H := Solvable.original_sylow_le_centralizer hzT
  have htwo : IsTwoLocal H := isTwoLocal_involution_centralizer
    (orderOf_eq_prime ((mem_omegaOneCenterAmbient_iff _ _).mp hzT).2.1 hz1)
  have horbit := Chapter1.Section02.component_normal_or_index_two_source
    (h₀.qtke.twoLocal_sqtk htwo) hK
  let S := T.subtype hTH
  let A := conjugateSpanBy K (S : Subgroup H)
  let Y := A.map H.subtype
  let : A.Normal := conjugateSpanBy_sylow_normal K S horbit
  let := hK.perfect
  let : Group.IsPerfect A := conjugateSpanBy_isPerfect K (S : Subgroup H)
  let : Group.IsPerfect Y := Group.IsPerfect.map H.subtype
  have hp : IsPPerfect 2 Y := by
    intro N hn hq
    let := hn
    let := hq.isNilpotent
    exact top_unique (le_of_isPerfect_of_solvable_quotient ⊤ N)
  have hnY : H ≤ normalizer (Y : Set G) := by
    have hh := (map_mono (show (⊤ : Subgroup H) ≤ normalizer (A : Set H)
      from le_normalizer_of_normal)).trans (A.le_normalizer_map H.subtype)
    simpa only [← MonoidHom.range_eq_map,range_subtype] using hh
  have hY : Y = conjugateSpanBy (K.map H.subtype) (T : Subgroup G) := by
    change (conjugateSpanBy K (S : Subgroup H)).map H.subtype = _
    rw [map_conjugateSpanBy,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH]
  intro hKM
  have h23 := ordinary_outside_twoThree_at h structural D m eL H ⟨Solvable.centralizer_mem_HOver hzT hz1,hout⟩ Y
    (map_subtype_le A) hnY hp
    (hY ▸ conjugateSpanBy_le hKM (D.sylow_normalizes_component.trans (normalizer (L : Set G)).le_normalizer))
  let : Group.IsSolvable Y := isSolvable_of_prime_dvd_card_eq_two_or_three _ (by
    intro p hp hd
    exact (IsPiGroup_iff _ _).mp h23 ⟨p,hp⟩ hd)
  let : Group.IsSolvable A := Group.isSolvable_of_isSolvable_injective
    (f := (A.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom)
    (A.equivMapOfInjective H.subtype H.subtype_injective).injective
  exact hK.not_isSolvable (Group.isSolvable_of_isSolvable_injective
    (f := inclusion (le_conjugateSpanBy K (S : Subgroup H))) (inclusion_injective _))

/-- Escape forces the component to move the actual reduced omega orbit. -/
private theorem escaping_component_faithful_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (m : CoreMarking D) {z : G}
    (hzT : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (K : Subgroup (centralizer ({z} : Set G))) (hK : K.IsCComponent)
    (hout : ¬ K.map (centralizer ({z} : Set G)).subtype ≤ normalizer (L : Set G)) :
    K.map (centralizer ({z} : Set G)).subtype ∈ MainForward.faithfulLocalComponents T := by
  let H := centralizer ({z} : Set G)
  let W := Solvable.centralizerOmegaOrbit T z
  let U := W.subgroupOf H
  have hWH : W ≤ H := Solvable.centralizerOmegaOrbit_le hzT
  have hred : IsPReduced 2 U := Solvable.centralizerOmegaOrbit_reduced h₀ hzT hz1
  let := hred.elementary
  have hU : U ≤ omegaOneCenterAmbient (pCore 2 H) := by
    intro u hu
    exact (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨hred.le_pCore hu,elemPow_eq_one_of_isElementaryAbelian u hu,
        hred.le_centralizer_pCore hu⟩
  have hm : ⁅U,K⁆ ≠ ⊥ := by
    intro he
    have hh := congrArg (Subgroup.map H.subtype) he
    rw [map_commutator,map_subgroupOf_eq_of_le hWH,Subgroup.map_bot] at hh
    have hc : K.map H.subtype ≤ centralizer (W : Set G) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hh)
    have hb : centralizer (W : Set G) ≤ normalizer (L : Set G) := by
      rw [←fixed_generator_centralizer_at h structural D m
        ⟨m.constant.property,m.constant_fixed⟩
        (fun he => m.constant_ne_one (Subtype.ext he))]
      apply centralizer_le
      exact Set.singleton_subset_iff.mpr (le_conjugateSpanBy _ _
        (m.constant_mem_central_four_at h structural).2)
    exact hout (hc.trans hb)
  exact (mem_faithfulLocalComponents_iff T _).mpr
    (Section03.Noncentrality.source_component_faithful_local T H
      (Solvable.original_sylow_le_centralizer hzT) (Solvable.centralizer_mem_HOver hzT hz1).1
      (Chapter1.lemma_1_1_4_6 T (h₀.qtke.evenCharacteristic T)
        (Solvable.centralizer_mem_HOver hzT hz1)) K U hK hU hm)

/-- Construct a relatively normal escaping component from the original centralizer. -/
theorem ordinary_exists_escaping_component_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    {z : G} (hzT : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (hout : ¬ centralizer ({z} : Set G) ≤ normalizer (L : Set G))
    (hnonsolv : ¬ Group.IsSolvable (centralizer ({z} : Set G))) :
    ∃ K : Subgroup G,
      K ∈ Chapter1.cComponentsIn (centralizer ({z} : Set G)) ∧
      K ∈ MainForward.faithfulLocalComponents T ∧
      K ∈ Chapter1.LStar G T ∧
      centralizer ({z} : Set G) ≤ normalizer (K : Set G) ∧
      (T : Subgroup G) ≤ normalizer (K : Set G) ∧
      ¬ K ≤ normalizer (L : Set G) ∧
      ¬ L ≤ normalizer (K : Set G) := by
  let H := centralizer ({z} : Set G)
  obtain ⟨K,hK⟩ := exists_isCComponent_of_not_isSolvable hnonsolv
  have he := relative_component_escape_at h₀ h structural m eL hzT hz1 hout K hK
  have hf := escaping_component_faithful_at h₀ h structural m hzT hz1 K hK he
  have hu := h.source_normalizer_maximal_unique_at structural
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have htwo : IsTwoLocal H := isTwoLocal_involution_centralizer
    (orderOf_eq_prime ((mem_omegaOneCenterAmbient_iff _ _).mp hzT).2.1 hz1)
  obtain ⟨hstar,hn,_,_,hLN,hKM⟩ :=
    Section03.SourceCompletion.unitary_component_normalizer_conclusions h₀.qtke T L H
      (Solvable.original_sylow_le_centralizer hzT) htwo D.sylow_normalizes_component
      hu.1 hu.2 hout h1332 K hK hf
  refine ⟨K.map H.subtype,⟨map_subtype_le _,?_⟩,hf,hstar,hn,(h1332 _ hf).1,hKM,hLN⟩
  change ((K.map H.subtype).comap H.subtype).IsCComponent
  rwa [comap_map_eq_self_of_injective H.subtype_injective]

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
