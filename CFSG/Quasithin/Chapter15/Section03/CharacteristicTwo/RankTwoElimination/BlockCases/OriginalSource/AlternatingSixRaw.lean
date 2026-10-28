module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.AlternatingSixFirstChoice
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.SixTransitiveFixed
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.AlternatingSixThompson
public import Theory.SpecificGroups.SymmetricSix.Parabolics.SynthemeTransitive
/-!
# Excluding the literal natural A6 row in original 15.3.21

The first source choice was already excluded by the actual orthogonal
order-nine image. In the second choice the image of J(R) selects the
syntheme parabolic in A6. The original theta subgroup has a nontrivial
two-perfect image normalized by this marked parabolic, hence is transitive
on the six letters. The natural-module cocycle calculation then puts the
original fixed plane in the centralizer of L, contrary to its normalizer
bound. The argument preserves both ordinary and triple component covers.

Source: Aschbacher–Smith 15.3.16–21, pp.1126–1127; C.2.3 and C.2.7.
-/

set_option backward.isDefEq.respectTransparency false
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]

private theorem component_star_residual_data
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hθ : theta (d.MI I) = d.Yplus) (hYL : d.Yplus ≤ c.L)
    (e : starImage c.L d.R c.L ≃* alternatingGroup (Fin 6)) :
    let b := e.toMonoidHom.comp (toStarImage c.L d.R)
    let A := (d.Yplus.subgroupOf c.L).map b
    let P := (d.M.subgroupOf c.L).map b
    A ≤ P ∧ A ≠ ⊥ ∧ IsPPerfect 2 A ∧ P ≤ normalizer (A : Set (alternatingGroup (Fin 6))) := by
  intro b A P
  have hYM : d.Yplus ≤ d.M := hθ ▸ (theta_le _).trans inf_le_left
  have hAP : A ≤ P := map_mono (comap_mono hYM)
  have hperm : IsPPerfect 2 (d.Yplus.subgroupOf c.L) :=
    (hθ ▸ ComponentIntersection.theta_isPPerfect (d.MI I)).of_surjective
      (subgroupOfEquivOfLe hYL).symm.toMonoidHom (subgroupOfEquivOfLe hYL).symm.surjective
  have hperfect : IsPPerfect 2 A := hperm.of_surjective
    (b.subgroupMap (d.Yplus.subgroupOf c.L)) (b.subgroupMap_surjective _)
  have hMY : d.M.subgroupOf c.L ≤ normalizer (d.Yplus.subgroupOf c.L : Set c.L) := by
    rw [←subgroupOf_normalizer_eq hYL]
    intro x hx
    rw [←hθ]
    exact normalizer_le_normalizer_theta _ ((d.MI I).le_normalizer ⟨hx,component_le c x.property⟩)
  have hn : P ≤ normalizer (A : Set (alternatingGroup (Fin 6))) :=
    (map_mono hMY).trans ((d.Yplus.subgroupOf c.L).le_normalizer_map b)
  have hgen : (⊤ : Subgroup c.L) = ⁅(⊤ : Subgroup c.L),d.Yplus.subgroupOf c.L⁆ := by
    apply map_injective c.L.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hYL, ←MonoidHom.range_eq_map,
      range_subtype]
    exact c.commutator_eq
  have hne : A ≠ ⊥ := by
    intro he
    have hh := congrArg (map b) hgen
    rw [map_commutator,show (d.Yplus.subgroupOf c.L).map b = ⊥ from he,
      commutator_bot_right] at hh
    have hb : Function.Surjective b := e.surjective.comp (toStarImage_surjective _ _)
    rw [←MonoidHom.range_eq_map,MonoidHom.range_eq_top.mpr hb] at hh
    exact top_ne_bot hh
  exact ⟨hAP,hne,hperfect,hn⟩

theorem alternatingSix_secondChoice_of_transitive
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (hsecond : OutsideStructure.SecondChoice d) :
    let C := starImage c.L d.R c.L
    let J := offenderSubgroup (starRepresentation c.L d.R)
    ∀ (hCJ : C ≤ J)
      (s : MovedSection ((starRepresentation c.L d.R).comp J.subtype) (C.subgroupOf J))
      (e : ActionEquiv (s.action.comp (C.subgroupOf J).subtype) (alternatingNatural 6)),
      let eC := (subgroupOfEquivOfLe hCJ).symm.trans e.groupEquiv
      let b := eC.toMonoidHom.comp (toStarImage c.L d.R)
      let A := (d.Yplus.subgroupOf c.L).map b
      (∀ i j : Fin 6, ∃ a : A, a.val.val i = j) → False := by
  intro C J hCJ s e eC b A ht
  have h := RankTwoElimination.OriginalSource.rankTwo_component_input_from_case
    hG d hempty hM hu hmany hI htwo hf c
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection
    hG d hempty hM hu hmany I hI
  have hrI : primeRank 3 I ≤ 2 :=
    (OutsideStructure.outside_sqtk hG d hI).stronglyQuasithin 3 (by decide) (by decide)
  have hYL : d.Yplus ≤ c.L := by
    rcases coreToStar_alternatingSix_alternatives d c h.normalizes eC with hOrd | ⟨_,hTri⟩
    · obtain ⟨f⟩ := hOrd
      exact yplus_le_of_alternatingSix_quotient d c h11.theta_eq.symm hrI f
    · obtain ⟨f⟩ := hTri
      exact yplus_le_of_hexacode_quotient d c h11.theta_eq.symm hrI f
  have hd := component_star_residual_data d c h11.theta_eq.symm hYL eC
  have hVW := RankTwoElimination.OriginalSource.component_seed_le_starV d h htwo.2.2.2.2.1
  have hYC : d.Yplus ≤ centralizer (d.V₁ : Set G) := by
    rw [hsecond.2]
    exact (map_subtype_le _).trans inf_le_right
  have hplane : d.V₁ ≤ centralizer (c.L : Set G) := by
    intro x hx
    obtain ⟨v,hv,hvx⟩ := hVW (d.action.plane_le 1 hx)
    change (v : G) = x at hvx
    let w : Additive (starV c.L d.R) := Additive.ofMul ⟨v,hv⟩
    have hw (a : A) : ((starRepresentation c.L d.R).comp J.subtype)
        (e.groupEquiv.symm a) w = w := by
      obtain ⟨y,hy,he⟩ := a.property
      have he' : e.groupEquiv.symm a =
          (subgroupOfEquivOfLe hCJ).symm (toStarImage c.L d.R y) := by
        apply e.groupEquiv.injective
        exact (e.groupEquiv.apply_symm_apply _).trans he.symm
      rw [he']
      change starRepresentation c.L d.R
        (QuotientGroup.mk' (starKernel c.L d.R) ⟨(y:G),mem_sup_left y.property⟩) w = w
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [starRepresentation_apply]
      apply Subtype.ext
      change (y:G)*(v:G)*(y:G)⁻¹ = (v:G)
      rw [hvx]
      exact mul_inv_eq_iff_eq_mul.mpr (hYC hy x hx).symm
    have hc := ChapterC.C27Source.star_alternatingSix_fixed_centralizes c.L d.R
      hCJ s e A hd.2.2.1 ht w hw
    exact hvx ▸ hc
  have hLN : c.L ≤ normalizer (d.V₁ : Set G) :=
    (le_centralizer_iff.mp hplane).trans (Subgroup.centralizer_le_normalizer _)
  exact c.outside (hLN.trans (h11.second_choice hsecond).2.1)

/-- The actual normalizer of the Thompson subgroup selects the syntheme
parabolic; its nontrivial two-perfect residual is transitive on six letters. -/
theorem source_15_3_21_alternatingSix_row_secondChoice
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (hsecond : OutsideStructure.SecondChoice d) :
    let C := starImage c.L d.R c.L
    let J := offenderSubgroup (starRepresentation c.L d.R)
    ∀ (_hCJ : C ≤ J)
      (s : MovedSection ((starRepresentation c.L d.R).comp J.subtype) (C.subgroupOf J))
      (_hgen : offenderSubgroup s.action = C.subgroupOf J)
      (e : ActionEquiv (s.action.comp (C.subgroupOf J).subtype) (alternatingNatural 6)),
      (∀ A, IsBestOffender s.action A → rank A = 2 ∧
        ∃ g : alternatingGroup (Fin 6),
          ((A.subgroupOf (C.subgroupOf J)).map
            ((alternatingGroup (Fin 6)).subtype.comp e.groupEquiv.toMonoidHom)) =
              (ChapterB.Offenders.evenPart 6).map
                (MulAut.conj (g : Equiv.Perm (Fin 6))).toMonoidHom) →
      quadraticRatio s.action = 1 → False := by
  intro C J hCJ s hgen e hoff hratio
  have h := RankTwoElimination.OriginalSource.rankTwo_component_input_from_case
    hG d hempty hM hu hmany hI htwo hf c
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection
    hG d hempty hM hu hmany I hI
  let eC := (subgroupOfEquivOfLe hCJ).symm.trans e.groupEquiv
  have hrI : primeRank 3 I ≤ 2 :=
    (OutsideStructure.outside_sqtk hG d hI).stronglyQuasithin 3 (by decide) (by decide)
  have hYL : d.Yplus ≤ c.L := by
    rcases coreToStar_alternatingSix_alternatives d c h.normalizes eC with hOrd | ⟨_,hTri⟩
    · obtain ⟨f⟩ := hOrd
      exact yplus_le_of_alternatingSix_quotient d c h11.theta_eq.symm hrI f
    · obtain ⟨f⟩ := hTri
      exact yplus_le_of_hexacode_quotient d c h11.theta_eq.symm hrI f
  have hd := component_star_residual_data d c h11.theta_eq.symm hYL eC
  obtain ⟨g,hg⟩ := ChapterC.C27Source.alternatingSix_marked_parabolic_from_source
    h hCJ s hgen e hoff hratio
  let q := toStarImage c.L d.R
  have hm : (d.M.subgroupOf c.L).map q =
      (starM c.L d.R (d.MI I)).subgroupOf C := by
    ext x
    constructor
    · rintro ⟨l,hl,rfl⟩
      exact ⟨⟨l,mem_sup_left l.property⟩,
        ⟨⟨hl,component_le c l.property⟩,l.property⟩,rfl⟩
    · rintro ⟨l,hl,he⟩
      refine ⟨⟨l,hl.2⟩,hl.1.1,?_⟩
      exact Subtype.ext he
  have hmap : (d.M.subgroupOf c.L).map (eC.toMonoidHom.comp q) =
      Theory.SpecificGroups.SymmetricSix.a6SynthemeStabilizer.map
        (MulAut.conjNormal g).toMonoidHom := by
    rw [←map_map,hm]
    exact hg
  have ht := Theory.SpecificGroups.SymmetricSix.conjugate_syntheme_normal_twoPerfect_transitive
    g ((d.Yplus.subgroupOf c.L).map (eC.toMonoidHom.comp q))
    (hmap ▸ hd.1) (hmap ▸ hd.2.2.2) hd.2.2.1 hd.2.1
  exact alternatingSix_secondChoice_of_transitive hG d hempty hM hu hmany hI htwo hf c
    hsecond hCJ s e ht

/-- The literal natural-A6 B.5 row is excluded in both original choices. -/
theorem source_15_3_21_alternatingSix_row
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    :
    let C := starImage c.L d.R c.L
    let J := offenderSubgroup (starRepresentation c.L d.R)
    ∀ (_hCJ : C ≤ J)
      (s : MovedSection ((starRepresentation c.L d.R).comp J.subtype) (C.subgroupOf J))
      (_hgen : offenderSubgroup s.action = C.subgroupOf J)
      (e : ActionEquiv (s.action.comp (C.subgroupOf J).subtype) (alternatingNatural 6)),
      (∀ A, IsBestOffender s.action A → rank A = 2 ∧
        ∃ g : alternatingGroup (Fin 6),
          ((A.subgroupOf (C.subgroupOf J)).map
            ((alternatingGroup (Fin 6)).subtype.comp e.groupEquiv.toMonoidHom)) =
              (ChapterB.Offenders.evenPart 6).map
                (MulAut.conj (g : Equiv.Perm (Fin 6))).toMonoidHom) →
      quadraticRatio s.action = 1 → False := by
  intro C J hCJ s hgen e hoff hratio
  rcases d.choice with hfirst | hsecond
  · exact source_15_3_21_alternatingSix_row_firstChoice
      hG d hempty hM hu hmany hI htwo hf c hfirst hCJ s e
  · exact source_15_3_21_alternatingSix_row_secondChoice
      hG d hempty hM hu hmany hI htwo hf c hsecond hCJ s hgen e hoff hratio

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
