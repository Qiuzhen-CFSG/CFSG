module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.AlternatingSixStarCover
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.OriginalGeometry
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.OriginalSource

/-!
# The first-choice A6 star exclusion in original 15.3.21

The actual component cover is either A6 or its triple cover; both put
Yplus in L. In the first choice Yplus=Y, its original orthogonal action
has image of order nine. Since V lies in the star omega-center, this
image is a quotient of Yplus*. But the proper marked star intersection
contains a component Sylow two-subgroup in A6, so its order divides 24.
The contradiction preserves the possible odd central covering kernel.

Source: Aschbacher--Smith 15.3.7, 15.3.16--21, printed pp.1122,1126--1127;
the proper star intersection is the original C.2.7 normalizer control.
-/
public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

theorem source_15_3_21_alternatingSix_star_firstChoice
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : starImage c.L d.R c.L ≃* alternatingGroup (Fin 6))
    (hfirst : d.Yplus = d.Y) : False := by
  have h := RankTwoElimination.OriginalSource.rankTwo_component_input_from_case
    hG d hempty hM hu hmany hI htwo hf c
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection
    hG d hempty hM hu hmany I hI
  have hrI : primeRank 3 I ≤ 2 :=
    (OutsideStructure.outside_sqtk hG d hI).stronglyQuasithin 3 (by decide) (by decide)
  have hYL : d.Yplus ≤ c.L := by
    rcases coreToStar_alternatingSix_alternatives d c h.normalizes e with hOrd | ⟨_,hTri⟩
    · obtain ⟨b⟩ := hOrd
      exact yplus_le_of_alternatingSix_quotient d c h11.theta_eq.symm hrI b
    · obtain ⟨b⟩ := hTri
      exact yplus_le_of_hexacode_quotient d c h11.theta_eq.symm hrI b
  have hYL' : d.Y ≤ c.L := hfirst ▸ hYL
  have hYM : d.Y ≤ d.M := Chapter14.SourcePreliminaries.sourceResidual_le _ _
  have hVW := RankTwoElimination.OriginalSource.component_seed_le_starV
    d h htwo.2.2.2.2.1
  let C := starImage c.L d.R c.L
  let q := toStarImage c.L d.R
  let m := (d.M.subgroupOf c.L).map q
  have hm : m = (starM c.L d.R (d.MI I)).subgroupOf C := by
    ext x
    constructor
    · rintro ⟨l,hl,rfl⟩
      exact ⟨⟨l,mem_sup_left l.property⟩,⟨⟨hl,component_le c l.property⟩,l.property⟩,rfl⟩
    · rintro ⟨l,hl,he⟩
      refine ⟨⟨l,hl.2⟩,hl.1.1,?_⟩
      exact Subtype.ext he
  have hmproper : m ≠ ⊤ := by
    intro he
    have hlt := (ChapterC.C27Source.star_thompson_intersection_from_source h).2
    have hall : C ≤ starM c.L d.R (d.MI I) := by
      intro x hx
      have hh : (⟨x,hx⟩ : C) ∈ m := he ▸ mem_top _
      rw [hm] at hh
      exact hh
    exact hlt.not_ge hall
  obtain ⟨P,hP⟩ := h11.sylow
  obtain ⟨Q,hQ⟩ := LinearThree.Extension.SourceCases.component_sylow d c P hP
  let b := e.toMonoidHom.comp q
  have hb : Function.Surjective b := e.surjective.comp (toStarImage_surjective _ _)
  have hmap : (d.M.subgroupOf c.L).map b = m.map e.toMonoidHom := by
    rw [map_map]
  have hmbot : (d.M.subgroupOf c.L).map b ≠ ⊤ := by
    rw [hmap]
    intro he
    apply hmproper
    have hh := (comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective m)
    rw [he,comap_top] at hh
    exact hh.symm
  have hQM : (Q : Subgroup c.L) ≤ d.M.subgroupOf c.L := by
    rw [hQ]
    exact fun _ hx => d.sylow_le hx.1
  have hcM := Theory.SpecificGroups.SymmetricSix.proper_sylow_overgroup_card_dvd_twenty_four
    (Q.mapSurjective hb) ((d.M.subgroupOf c.L).map b) (map_mono hQM) hmbot
  let f := d.action.actor.comp (inclusion hYM)
  let g := b.comp (inclusion hYL')
  have hker : g.ker ≤ f.ker := by
    intro y hy
    have hq : q (inclusion hYL' y) = 1 := e.map_eq_one_iff.mp hy
    have hq' := congrArg Subtype.val hq
    have hyK : (⟨(y : G),mem_sup_left (hYL' y.property)⟩ : (c.L ⊔ d.R : Subgroup G)) ∈
        starKernel c.L d.R := (QuotientGroup.eq_one_iff _).mp hq'
    have hyC : (y : G) ∈ centralizer (d.V : Set G) := by
      intro v hv
      obtain ⟨w,hw,he⟩ := hVW hv
      have hh := hyK w hw
      exact he ▸ congrArg Subtype.val hh
    change inclusion hYM y ∈ d.action.actor.ker
    rw [d.action.ker_actor]
    exact hyC
  have hrange : f.range = d.action.image d.Y := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact ⟨inclusion hYM y,y.property,rfl⟩
    · rintro ⟨y,hy,rfl⟩
      exact ⟨⟨y,hy⟩,rfl⟩
  have hgM : g.range ≤ (d.M.subgroupOf c.L).map b := by
    rintro _ ⟨y,rfl⟩
    exact ⟨inclusion hYL' y,hYM y.property,rfl⟩
  have hd : Nat.card f.range ∣ Nat.card g.range := by
    have hh := relIndex_dvd_of_le_left (⊤ : Subgroup d.Y) hker
    simpa only [relIndex_ker,←MonoidHom.range_eq_map] using hh
  obtain ⟨hne,_,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  have hi := (source_lemma_15_3_7_of_orthogonal_action
    hG d.T hempty d.action hM hu hmany hne).1
  have hcard : Nat.card f.range = 9 := by
    rw [hrange,show d.action.image d.Y = Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor) from hi]
    exact RankTwo.orthogonal_twoResidual_card
  have hh : 9 ∣ 24 := hcard ▸ hd.trans ((card_dvd_of_le hgM).trans hcM)
  norm_num at hh

/-- The literal natural-A6 moved row feeds the first-choice star exclusion. -/
theorem source_15_3_21_alternatingSix_row_firstChoice
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (hfirst : d.Yplus = d.Y) :
    let C := starImage c.L d.R c.L
    let J := Representation.BinaryOffender.offenderSubgroup (starRepresentation c.L d.R)
    ∀ (_hCJ : C ≤ J)
      (s : ChapterB.QuasisimpleSource.MovedSection
        ((starRepresentation c.L d.R).comp J.subtype) (C.subgroupOf J)),
      ChapterB.QuasisimpleSource.ActionEquiv (s.action.comp (C.subgroupOf J).subtype)
        (ChapterB.QuasisimpleSource.alternatingNatural 6) → False := by
  intro C J hCJ s e
  exact source_15_3_21_alternatingSix_star_firstChoice hG d hempty hM hu hmany hI htwo hf c
    ((subgroupOfEquivOfLe hCJ).symm.trans e.groupEquiv) hfirst
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
