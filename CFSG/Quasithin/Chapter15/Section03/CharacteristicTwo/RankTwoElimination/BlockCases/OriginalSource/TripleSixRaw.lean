module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.TripleSixRawSeed
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.TripleSixFixed
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.TripleSixRawPlanes
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.PlaneActors.Geometry

/-!
# Excluding the raw triple-six row in original 15.3.21

The actual core-to-star covering is an isomorphism of triple covers of A₆.
Its cubic center lies in the image of the original rank-two theta actor.
The faithful irreducible moved quotient has no cubic fixed vectors, so its
central projection is injective. In the first source choice the original
sixteen embeds in this quotient. The cubic action forces an element of
quotient order four to fix both marked planes, contradicting the F₄³ bound.
The second choice is excluded by the built cubic fixed-vector centralization
argument and the original plane-normalizer bound.

The final consumer retains the original ambient hypotheses and all literal
B.5 section maps. The irreducible constructor supplies its three action
hypotheses; no exceptional-block reconstruction or kernel assumption is used.

Source: Aschbacher–Smith 15.3.17 and 15.3.21, pp.1126–1127; B.5.1,
pp.99–103; B.4.2(8), p.86, and K.1.3, p.453.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve.SourceInterface ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]

private theorem tripleSix_core_sylow_four {A : Type*} [Group A] [Finite A]
    (f : (A ⧸ pCore 2 A) →* alternatingGroup (Fin 6)) (hf : Function.Surjective f)
    (P : Sylow 2 A) :
    ∃ t : A, t ∈ (P : Subgroup A) ∧ orderOf (QuotientGroup.mk' (pCore 2 A) t) = 4 := by
  let q := QuotientGroup.mk' (pCore 2 A)
  obtain ⟨x,hx⟩ := TripleSixFixedSpace.cover_has_four f hf
  have hp : IsPGroup 2 (zpowers x) := by
    apply IsPGroup.of_card_dvd_pow (n := 2)
    rw [Nat.card_zpowers,hx]
    decide
  obtain ⟨Q,hQ⟩ := hp.exists_le_sylow
  let Pbar := P.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  let v : Pbar := Q.equiv Pbar ⟨x,hQ (mem_zpowers x)⟩
  have hv : orderOf (v : A ⧸ pCore 2 A) = 4 := by
    rw [orderOf_coe]
    exact ((Q.equiv Pbar).orderOf_eq _).trans (by simpa only [←Subgroup.orderOf_coe] using hx)
  obtain ⟨t,ht,heq⟩ := v.property
  exact ⟨t,ht,heq ▸ hv⟩

theorem tripleSix_firstChoice_of_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (c : ComponentWitness d I) (hR : d.R ≤ normalizer (c.L:Set G))
    (hYL : d.Yplus ≤ c.L) (hc : Nat.card (center (c.L ⧸ pCore 2 c.L))=3)
    (hinj : Function.Injective (coreToStar hR))
    (hVW : d.V ≤ (starV c.L d.R).map (c.L ⊔ d.R : Subgroup G).subtype)
    (hcomm : d.V=⁅d.V,d.Yplus⁆) (hfirst : d.Yplus=d.Y)
    (T : Sylow 2 c.L) (hT : (T : Subgroup c.L)=d.S.subgroupOf c.L) :
    let C := starImage c.L d.R c.L
    let J := offenderSubgroup (starRepresentation c.L d.R)
    ∀ (_hCJ : C ≤ J)
      (s : MovedSection ((starRepresentation c.L d.R).comp J.subtype) (C.subgroupOf J)),
      IsIrrPlus ((starRepresentation c.L d.R).comp J.subtype) (C.subgroupOf J)
        s.space.toSubmodule → Function.Injective s.action →
      IsIrreducible (s.action.comp (C.subgroupOf J).subtype) →
      ChapterB.SourceInduction.ProjectiveLine.TripleSixAction s.action (C.subgroupOf J) → False := by
  intro C J hCJ s hi hfaith hir a
  let Q := c.L ⧸ pCore 2 c.L
  let q := QuotientGroup.mk' (pCore 2 c.L)
  let e : Q ≃* C.subgroupOf J :=
    (MulEquiv.ofBijective (coreToStar hR) ⟨hinj,coreToStar_surjective hR⟩).trans
      (subgroupOfEquivOfLe hCJ).symm
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := center Q) 3 (by rw [hc])
  have hz1 : (z : Q) ≠ 1 := by
    intro hh
    have he : z=1 := Subtype.ext hh
    rw [he,orderOf_one] at hz
    contradiction
  have hz3 : (z : Q)^3=1 := congrArg Subtype.val (hz ▸ pow_orderOf_eq_one z)
  let z0 := e z
  have hz0 : z0 ∈ center (C.subgroupOf J) := (centerCongr e z).property
  have hz01 : z0 ≠ 1 := fun hh => hz1 (e.map_eq_one_iff.mp hh)
  have hz03 : z0^3=1 := by rw [←map_pow,hz3,map_one]
  obtain ⟨y,hy,hyz⟩ := source_rankTwo_cubic_center_le_image hG d hI htwo c hYL hc z.property
  have hp := s.centralProjection_injective_of_cubic hi hfaith hir z0 hz0 hz01 hz03
  obtain ⟨j,hj,hj1,hja⟩ := tripleSix_seed_embedding d c hYL hVW hcomm hCJ s hp
  have hact (l : c.L) (hl : (l:G)∈normalizer (d.V:Set G)) (v:d.V) :
      j (d.V.normalizerMonoidHom ⟨l,hl⟩ v)=s.central.quotientRepresentation (e (q l)) (j v) := by
    have he : e (q l)=(subgroupOfEquivOfLe hCJ).symm (toStarImage c.L d.R l) := by
      change (subgroupOfEquivOfLe hCJ).symm (coreToStar hR (q l)) = _
      rw [coreToStar_mk]
    exact (hja l hl v).trans (congrArg (fun u : C.subgroupOf J =>
      s.central.quotientRepresentation (u:J) (j v)) he.symm)
  let f : Q →* alternatingGroup (Fin 6) :=
    a.quotientEquiv.toMonoidHom.comp ((QuotientGroup.mk' (center (C.subgroupOf J))).comp e.toMonoidHom)
  obtain ⟨t,ht,ht4⟩ := tripleSix_core_sylow_four f
    (a.quotientEquiv.surjective.comp ((QuotientGroup.mk'_surjective _).comp e.surjective)) T
  have htS : (t:G)∈d.S := by
    change t∈d.S.subgroupOf c.L
    rw [←hT]
    exact ht
  exact tripleSix_firstChoice_plane_contradiction d c.L (C.subgroupOf J)
    s.central.quotientRepresentation (e.toMonoidHom.comp q) a
    (hfaith.comp Subtype.val_injective) hir hfirst j hj hj1 hact y t hy htS
    (by change e (q y)∈center (C.subgroupOf J); rw [hyz]; exact hz0)
    (by change e (q y)≠1; rw [hyz]; exact hz01)
    (by change (e (q y))^3=1; rw [hyz]; exact hz03)
    ((e.orderOf_eq _).trans ht4)

/-- The actual raw triple-six moved action excludes the first source choice. -/
theorem source_tripleSix_firstChoice
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I) (hfirst : d.Yplus = d.Y) :
    let C := starImage c.L d.R c.L
    let J := offenderSubgroup (starRepresentation c.L d.R)
    ∀ (_hCJ : C ≤ J)
      (qsrc : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        ((starRepresentation c.L d.R).comp J.subtype) (C.subgroupOf J)),
      IsIrrPlus ((starRepresentation c.L d.R).comp J.subtype) (C.subgroupOf J)
        qsrc.sectionData.space.toSubmodule →
      Function.Injective qsrc.sectionData.action →
      IsIrreducible (qsrc.sectionData.action.comp (C.subgroupOf J).subtype) →
      ChapterB.SourceInduction.ProjectiveLine.TripleSixAction qsrc.sectionData.action (C.subgroupOf J) →
      False := by
  intro C J hCJ qsrc hi hfaith hir a
  obtain ⟨hR,hinj,hc,⟨eCore⟩⟩ := source_tripleSix_core_data
    hG d hempty hM hu hmany hI htwo hf c hCJ qsrc a
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection
    hG d hempty hM hu hmany I hI
  have hYL := yplus_le_of_tripleSix_core d c h11.theta_eq.symm
    ((OutsideStructure.outside_sqtk hG d hI).stronglyQuasithin 3 (by decide) (by decide)) eCore
  have hinput := RankTwoElimination.OriginalSource.rankTwo_component_input_from_case
    hG d hempty hM hu hmany hI htwo hf c
  have hVW := RankTwoElimination.OriginalSource.component_seed_le_starV
    d hinput htwo.2.2.2.2.1
  have hcomm : d.V = ⁅d.V,d.Yplus⁆ := by
    obtain ⟨hne,_,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
      hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
    obtain ⟨hi,_,_,_⟩ := source_lemma_15_3_7_of_orthogonal_action
      hG d.T hempty d.action hM hu hmany hne
    rw [hfirst]
    exact (d.action.commutator_eq_of_residual_image d.Y
      (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc) hi).symm
  obtain ⟨P,hP⟩ := h11.sylow
  obtain ⟨T,hT⟩ := LinearThree.Extension.SourceCases.component_sylow d c P hP
  exact tripleSix_firstChoice_of_core hG d hI htwo c hR hYL hc hinj hVW hcomm hfirst
    T hT hCJ qsrc.sectionData hi hfaith hir a

/-- The literal B.5 triple-six row contradicts either original source choice. -/
theorem source_15_3_21_tripleSix_row
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I) :
    let C := starImage c.L d.R c.L
    let J := offenderSubgroup (starRepresentation c.L d.R)
    ∀ (_hCJ : C ≤ J)
      (qsrc : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        ((starRepresentation c.L d.R).comp J.subtype) (C.subgroupOf J)),
      IsIrrPlus ((starRepresentation c.L d.R).comp J.subtype) (C.subgroupOf J)
        qsrc.sectionData.space.toSubmodule →
      Function.Injective qsrc.sectionData.action →
      IsIrreducible (qsrc.sectionData.action.comp (C.subgroupOf J).subtype) →
      ChapterB.SourceInduction.ProjectiveLine.TripleSixAction qsrc.sectionData.action (C.subgroupOf J) →
      False := by
  intro C J hCJ qsrc hi hfaith hir a
  rcases d.choice with hfirst | hsecond
  · exact source_tripleSix_firstChoice hG d hempty hM hu hmany hI htwo hf c hfirst
      hCJ qsrc hi hfaith hir a
  · exact source_tripleSix_secondChoice hG d hempty hM hu hmany hI htwo hf c hsecond
      hCJ qsrc hi hfaith hir a

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
