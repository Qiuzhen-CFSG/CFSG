module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.TripleSixRawCover
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedCubic

/-!
# Cubic fixed vectors in the original triple-six row

The true core cover puts the cubic center in the rank-two theta image.
On the faithful irreducible moved quotient this cubic has zero norm.
Commutator generation lifts that relation to the actual moved space, so
an ambient vector fixed by the cubic centralizes the entire component.
The second source choice then contradicts the original marked-plane
normalizer bound, without reconstructing an exceptional block.

Source: Aschbacher–Smith 15.3.17 and 15.3.21, pp.1126–1127; B.5.1.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve.SourceInterface ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]

theorem tripleSix_star_fixed_centralizes
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (c : ComponentWitness d I) (hR : d.R ≤ normalizer (c.L : Set G))
    (hYL : d.Yplus ≤ c.L) (hc : Nat.card (center (c.L ⧸ pCore 2 c.L)) = 3)
    (hinj : Function.Injective (coreToStar hR)) :
    let C := starImage c.L d.R c.L
    let J := offenderSubgroup (starRepresentation c.L d.R)
    ∀ (_hCJ : C ≤ J)
      (s : MovedSection ((starRepresentation c.L d.R).comp J.subtype) (C.subgroupOf J)),
      IsIrrPlus ((starRepresentation c.L d.R).comp J.subtype) (C.subgroupOf J) s.space.toSubmodule →
      Function.Injective s.action → IsIrreducible (s.action.comp (C.subgroupOf J).subtype) →
      ∀ x : G, x ∈ (starV c.L d.R).map (c.L ⊔ d.R : Subgroup G).subtype →
        x ∈ centralizer (d.Yplus : Set G) → x ∈ centralizer (c.L : Set G) := by
  intro C J hCJ s hi hfaith hir x hx hxy
  let j : C ≃* C.subgroupOf J := (subgroupOfEquivOfLe hCJ).symm
  let e : (c.L ⧸ pCore 2 c.L) ≃* C.subgroupOf J :=
    (MulEquiv.ofBijective (coreToStar hR) ⟨hinj,coreToStar_surjective hR⟩).trans j
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := center (c.L ⧸ pCore 2 c.L)) 3 (by rw [hc])
  have hz1 : (z : c.L ⧸ pCore 2 c.L) ≠ 1 := by
    intro hh
    have he : z = 1 := Subtype.ext hh
    rw [he,orderOf_one] at hz
    contradiction
  have hz3 : (z : c.L ⧸ pCore 2 c.L)^3 = 1 := congrArg Subtype.val (hz ▸ pow_orderOf_eq_one z)
  obtain ⟨y,hy,hyz⟩ := source_rankTwo_cubic_center_le_image hG d hI htwo c hYL hc z.property
  let z0 := e z
  have hz0 : z0 ∈ center (C.subgroupOf J) := (centerCongr e z).property
  have hz01 : z0 ≠ 1 := fun hh => hz1 (e.map_eq_one_iff.mp hh)
  have hz03 : z0^3 = 1 := by rw [←map_pow,hz3,map_one]
  obtain ⟨v,hv,rfl⟩ := hx
  let w : Additive (starV c.L d.R) := Additive.ofMul ⟨v,hv⟩
  have hcoez : ((z0 : J) : StarQuotient c.L d.R) =
      QuotientGroup.mk' (starKernel c.L d.R) ⟨y,mem_sup_left y.property⟩ := by
    change ((coreToStar hR (z : c.L ⧸ pCore 2 c.L) : C) : StarQuotient c.L d.R) = _
    rw [←hyz,coreToStar_mk]
    rfl
  have hzw : ((starRepresentation c.L d.R).comp J.subtype) z0 w = w := by
    change starRepresentation c.L d.R (z0 : StarQuotient c.L d.R) w = w
    rw [hcoez]
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [starRepresentation_apply]
    apply Subtype.ext
    change (y:G)*(v:G)*(y:G)⁻¹ = (v:G)
    exact mul_inv_eq_iff_eq_mul.mpr (hxy y hy)
  have hfixed := s.fixed_of_central_cubic hi hfaith hir z0 hz0 hz01 hz03 w hzw
  intro l hl
  let lL : c.L := ⟨l,hl⟩
  let l0 := j (toStarImage c.L d.R lL)
  have hh := hfixed l0
  change starRepresentation c.L d.R ((l0 : J) : StarQuotient c.L d.R) w = w at hh
  have hcl : ((l0 : J) : StarQuotient c.L d.R) =
      QuotientGroup.mk' (starKernel c.L d.R) ⟨l,mem_sup_left hl⟩ := rfl
  rw [hcl] at hh
  have he := congrArg (fun v : Additive (starV c.L d.R) => ((v.toMul : (c.L ⊔ d.R : Subgroup G)) : G)) hh
  rw [starRepresentation_apply] at he
  exact (mul_inv_eq_iff_eq_mul.mp he)



theorem yplus_le_of_tripleSix_core
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hθ : theta (d.MI I) = d.Yplus) (hrI : primeRank 3 I ≤ 2)
    (f : (c.L ⧸ pCore 2 c.L) ≃* Atlas.Codes.HexEvenAutomorphisms) : d.Yplus ≤ c.L := by
  let K := c.L.subgroupOf I
  let a : K ≃* c.L := subgroupOfEquivOfLe (component_le c)
  let b : (K ⧸ pCore 2 K) ≃* Atlas.Codes.HexEvenAutomorphisms :=
    (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans f
  have hYN : d.Yplus ≤ normalizer (c.L : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr c.commutator_eq.ge
  have hYNK : d.Yplus.subgroupOf I ≤ normalizer (K : Set I) := by
    rw [←subgroupOf_normalizer_eq (component_le c)]
    exact comap_mono hYN
  rw [←hθ]
  apply (closure_le _).mpr
  rintro x ⟨hx,hx3⟩
  let y : I := ⟨x,hx.2⟩
  have hy3 : orderOf y = 3 := by simpa only [←Subgroup.orderOf_coe] using hx3
  have hyN : y ∈ normalizer (K : Set I) :=
    hYNK (hθ ▸ subset_closure ⟨hx,hx3⟩)
  exact HexacodeTheta.order_three_mem K
    (LinearThree.Extension.SourceCases.component_in_overgroup d c) b hrI hy3 hyN

/-- The actual irreducible triple-six row excludes the second source choice. -/
theorem source_tripleSix_secondChoice
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
      (qsrc : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        ((starRepresentation c.L d.R).comp J.subtype) (C.subgroupOf J)),
      IsIrrPlus ((starRepresentation c.L d.R).comp J.subtype) (C.subgroupOf J)
        qsrc.sectionData.space.toSubmodule →
      Function.Injective qsrc.sectionData.action →
      IsIrreducible (qsrc.sectionData.action.comp (C.subgroupOf J).subtype) →
      ChapterB.SourceInduction.ProjectiveLine.TripleSixAction qsrc.sectionData.action (C.subgroupOf J) →
      False := by
  intro C J hCJ qsrc hi hfaith hir a
  obtain ⟨hR,hinj,hc,⟨e⟩⟩ := source_tripleSix_core_data
    hG d hempty hM hu hmany hI htwo hf c hCJ qsrc a
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection
    hG d hempty hM hu hmany I hI
  have hYL := yplus_le_of_tripleSix_core d c h11.theta_eq.symm
    ((OutsideStructure.outside_sqtk hG d hI).stronglyQuasithin 3 (by decide) (by decide)) e
  have hinput := RankTwoElimination.OriginalSource.rankTwo_component_input_from_case
    hG d hempty hM hu hmany hI htwo hf c
  have hVW := RankTwoElimination.OriginalSource.component_seed_le_starV
    d hinput htwo.2.2.2.2.1
  have hYC : d.Yplus ≤ centralizer (d.V₁ : Set G) := by
    rw [hsecond.2]
    exact (map_subtype_le _).trans inf_le_right
  have hplane : d.V₁ ≤ centralizer (c.L : Set G) := by
    intro x hx
    exact tripleSix_star_fixed_centralizes hG d hI htwo c hR hYL hc hinj
      hCJ qsrc.sectionData hi hfaith hir x (hVW (d.action.plane_le 1 hx))
      (fun y hy => (hYC hy x hx).symm)
  have hLN : c.L ≤ normalizer (d.V₁ : Set G) :=
    (le_centralizer_iff.mp hplane).trans (Subgroup.centralizer_le_normalizer _)
  exact c.outside (hLN.trans (h11.second_choice hsecond).2.1)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
