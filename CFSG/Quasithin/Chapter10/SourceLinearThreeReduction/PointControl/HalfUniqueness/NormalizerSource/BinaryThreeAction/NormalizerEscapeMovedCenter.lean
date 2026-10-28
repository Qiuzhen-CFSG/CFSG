module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.NormalizerEscapeBinaryInput
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.ExactDistanceFour
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.DistanceEightCenter
public import CFSG.Quasithin.Chapter10.SourceA5PointQuasisimple

/-!
# The original natural factor is the moved center of the full MS core

The first selected natural factor lies centrally in the original intrinsic
commutator core. Its full movement puts it inside the moved center. For a
nonabelian core, both actual MS distance branches bound that moved center
by eight: distance four identifies the entire center with a natural module,
and above four the original source identifies its moving summand with one.
The original factor also has order eight, so the two literal subgroups agree.
No whole-core order, fixed-factor equality, or normalization conclusion is
assumed. Source: Aschbacher--Smith 10.2.5 and C.1.34, pp.748 and136--137.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction
open Chapter3.Section02 ChapterC.BinaryMS
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
local notation "msCenter" => Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn

private theorem natural_section_card {J : Type*} [Group J]
    {A U : Subgroup J} {a : A →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    (hm : HasSectionModel A U ⊥ a (Representation.specialLinearNatural (k := ZMod 2) 3)) :
    Nat.card U = 8 := by
  obtain ⟨_,_,_,hn,e,_⟩ := hm
  let := hn
  let q : U ≃* Multiplicative (Fin 3 → ZMod 2) :=
    QuotientGroup.quotientBot.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (bot_subgroupOf U).symm).trans e)
  rw [Nat.card_congr q.toEquiv]
  change Nat.card (Fin 3 → ZMod 2) = 8
  simp only [Nat.card_fun,Nat.card_fin,Nat.card_zmod]
  norm_num

private theorem nonabelian_moved_center_card_le {J : Type*} [Group J] [Finite J]
    {κ : GroupClass} {A R : Subgroup J} (h : Input κ A R)
    (hc : ¬ IsMulCommutative (commutatorCore A)) :
    Nat.card (⁅msCenter (commutatorCore A),A⁆ : Subgroup J) ≤ 8 := by
  obtain ⟨t⟩ := MS93.exists_setup h hc
  obtain ⟨common⟩ := t.commonFacts hc
  have hQ : msQ A R = commutatorCore A := by
    rw [msQ,h.sup_eq_top]
    rw [show (⊤ : Subgroup J).pCoreIn 2 = pCore 2 J from pCore_map_iso 2 topEquiv]
  by_cases hb : t.geometry.b t.reduction.radical = 4
  · have hm := (t.sectionModels_of_distance_four common hb).1
    change HasSectionModel A (msCenter (msQ A R)) ⊥ _ _ at hm
    rw [hQ] at hm
    have hcard := natural_section_card hm
    have hle : ⁅msCenter (commutatorCore A),A⁆ ≤ msCenter (commutatorCore A) :=
      le_normalizer_iff_commutator_le_left.mp hm.2.1
    exact (card_le_of_le hle).trans hcard.le
  · have heven := t.geometry.even (MS93.alpha t.reduction.radical) rfl
    change Even (t.geometry.b t.reduction.radical) at heven
    obtain ⟨n,hn⟩ := heven
    have hlarge : 4 < t.geometry.b t.reduction.radical := by
      have := common.large_distance
      omega
    have hm := (t.center_source_sections common hlarge).2.2.2
    change HasSectionModel A (⁅msCenter (msQ A R),A⁆) ⊥ _ _ at hm
    rw [hQ] at hm
    exact (natural_section_card hm).le

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The original selected moved factor belongs to the center of the full
binary MS core, through the literal inclusion in G. -/
theorem normalizerEscape_moved_le_core_center
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      D.maximalLocal)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    let J := L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))
    ⁅D.fullModule,L⁆ ≤ (msCenter (commutatorCore (L.subgroupOf J))).map J.subtype := by
  let J := L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))
  let A := L.subgroupOf J
  let C := commutatorCore A
  let C₀ := (⁅pCore 2 L,(⊤ : Subgroup L)⁆).map L.subtype
  have hmap : C.map J.subtype = C₀ := normalizerEscape_commutatorCore_map D hn hout e
  have hC : C₀ ≤ L.pCoreIn 2 := by
    exact map_mono (commutator_le_left _ _)
  have hWC : ⁅D.fullModule,L⁆ ≤ C₀ := by
    have hh := commutator_mono (source_full_moved_le_component_core D) (le_refl L)
    rw [source_full_moved_eq_commutator D] at hh
    simpa only [C₀,Subgroup.pCoreIn,map_commutator,← MonoidHom.range_eq_map,range_subtype] using hh
  have hWZ : ⁅D.fullModule,L⁆ ≤ msCenter C₀ := by
    intro w hw
    refine ⟨⟨w,hWC hw⟩,mem_center_iff.mpr ?_,rfl⟩
    intro c
    exact Subtype.ext ((source_component_core_centralizes_fullModule D (hC c.property))
      w ((le_normalizer_iff_commutator_le_left.mp
        (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
          D.maximalLocal_normalizes_fullModule)) hw)).symm
  change ⁅D.fullModule,L⁆ ≤ (msCenter C).map J.subtype
  rw [←centerIn_map C J.subtype J.subtype_injective,hmap]
  exact hWZ

/-- In the genuine nonabelian branch the original natural factor exhausts
the moved center of the full core. The abelian branch is kept separate. -/
theorem normalizerEscape_moved_center_eq
    (s : NaturalData D)
    (hout : ¬ normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      D.maximalLocal)
    (hc : ¬ IsMulCommutative (commutatorCore
      (L.subgroupOf (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G)))))) :
    let J := L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))
    ⁅D.fullModule,L⁆ = (⁅msCenter (commutatorCore (L.subgroupOf J)),
      L.subgroupOf J⁆).map J.subtype := by
  let J := L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))
  let A := L.subgroupOf J
  let C := commutatorCore A
  let h := normalizerEscapeBinaryInput D (selected_nonnormal s) hout s.quotient
  have hbound : Nat.card ((⁅msCenter C,A⁆).map J.subtype) ≤ 8 := by
    rw [card_map_of_injective J.subtype_injective]
    exact nonabelian_moved_center_card_le h hc
  have hle : ⁅D.fullModule,L⁆ ≤ (⁅msCenter C,A⁆).map J.subtype := by
    have hh := commutator_mono
      (normalizerEscape_moved_le_core_center D (selected_nonnormal s) hout s.quotient)
      (le_refl L)
    rw [source_full_moved_eq_commutator D] at hh
    rw [map_commutator,map_subgroupOf_eq_of_le (show L ≤ J from le_sup_left)]
    exact hh
  apply eq_of_le_of_card_ge hle
  rw [moved_card s s.fixed_zero]
  exact hbound

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction
