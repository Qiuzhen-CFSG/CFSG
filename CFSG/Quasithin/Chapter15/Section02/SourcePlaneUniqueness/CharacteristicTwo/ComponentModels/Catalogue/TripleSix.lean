module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.AlternatingPlacement
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.LinearThree.Descent
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.DualExtensions.Reduction
public import Theory.GroupTheory.PrimeRankNormalIntersection

/-!
# Excluding the original triple-six component action

Ratio one transfers the original offender generation to the moved section.
The triple-six generated-component clause therefore puts the original
Thompson image inside X*. The cubic center of X* centralizes that image,
so the source normalizer control places it in the marked NI intersection.

The source bounds the center of X/O₂(X) by three. Its central quotient
is already identified with that of X*, so the literal core-to-star map
is injective. This lifts center placement to the original central
preimage in X. Quasithinness forces its intersection with the original
rank-two K to have order divisible by three, contradicting K ∩ M = O₂(K).
The actual triple-six action discharges every extra premise; the original
X, R, NI and moved section are preserved.

Source: Aschbacher--Smith original 15.2.23, pp.1116--1117, C.2.7,
pp.145--147, and B.5.1(5), pp.102--103; refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory PerfectCentralCovering Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
open Section01 PlaneUniquenessPreceding PlaneUniquenessPreceding.LinearThree TerminalLinear
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource ChapterB.SourceInduction.ProjectiveLine
variable {G : Type*} [Group G] [Finite G] {I X R N : Subgroup G}

/-- A cubic star center exhausts the source bound on the core center,
so the literal core-to-star covering is an isomorphism. -/
noncomputable def cubicCenterCoreStarEquiv
    (h : Input KnownSimple.IsKnownSimple I R N X)
    (hz : Nat.card (center (starImage X R X)) = 3) :
    (X ⧸ pCore 2 X) ≃* starImage X R X := by
  have hc : Nat.card (center (X ⧸ pCore 2 X)) ≤ Nat.card (center (starImage X R X)) := by
    rcases coreQuotient_center_card_from_source h with hh | hh <;> omega
  have hd : Nat.card (X ⧸ pCore 2 X) ≤ Nat.card (starImage X R X) := by
    rw [card_eq_card_quotient_mul_card_subgroup (center (X ⧸ pCore 2 X)),
      card_eq_card_quotient_mul_card_subgroup (center (starImage X R X)),
      Nat.card_congr (coreStarCenterEquiv h).toEquiv]
    exact Nat.mul_le_mul_left _ hc
  exact MulEquiv.ofBijective (coreToStar h.normalizes)
    ((coreToStar_surjective h.normalizes).bijective_of_nat_card_le hd)

/-- The center of the actual star component centralizes the original
Thompson image and hence lies in the marked intersection. -/
theorem star_center_le_marked_intersection_of_thompson_inner
    (h : Input KnownSimple.IsKnownSimple I R N X)
    (hinner : starImage X R (elementaryAbelianMaxJ R) ≤ starImage X R X) :
    center (starImage X R X) ≤ (starM X R N).subgroupOf (starImage X R X) := by
  intro x hx
  apply (star_thompson_intersection_from_source h).1
  refine ⟨x.property,Subgroup.centralizer_le_normalizer _ ?_⟩
  intro j hj
  exact congrArg Subtype.val (mem_center_iff.mp hx ⟨j,hinner hj⟩)

/-- The core center lies in the original NI image under the literal
two-core quotient map. -/
theorem cubic_core_center_le_marked_intersection
    (h : Input KnownSimple.IsKnownSimple I R N X)
    (hz : Nat.card (center (starImage X R X)) = 3)
    (hinner : starImage X R (elementaryAbelianMaxJ R) ≤ starImage X R X) :
    center (X ⧸ pCore 2 X) ≤
      (N.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X)) := by
  let a := cubicCenterCoreStarEquiv h hz
  intro z hz'
  have ht := star_center_le_marked_intersection_of_thompson_inner h hinner
    ((centerCongr a) ⟨z,hz'⟩).property
  obtain ⟨g,hg,he⟩ := ht
  let x : X := ⟨g.val,hg.2⟩
  have he' : toStarImage X R x = a z := Subtype.ext he
  refine ⟨x,hg.1,?_⟩
  apply a.injective
  change coreToStar h.normalizes (QuotientGroup.mk' (pCore 2 X) x) = _
  rw [coreToStar_mk]
  exact he'

/-- Ratio one transfers offender generation to the actual moved section,
placing the original Thompson image inside the component. -/
theorem ratio_one_thompson_inner_of_generated_component
    (h : Input KnownSimple.IsKnownSimple I R N X)
    (_hCJ : starImage X R X ≤ offenderSubgroup (starRepresentation X R))
    (s : MovedSection ((starRepresentation X R).comp (offenderSubgroup (starRepresentation X R)).subtype)
      ((starImage X R X).subgroupOf (offenderSubgroup (starRepresentation X R))))
    (hgen : offenderSubgroup s.action =
      (starImage X R X).subgroupOf (offenderSubgroup (starRepresentation X R)))
    (hr : quadraticRatio s.action = 1) :
    starImage X R (elementaryAbelianMaxJ R) ≤ starImage X R X := by
  let : (X.subgroupOf (X ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le le_normalizer h.normalizes)
  let : (starImage X R X).Normal :=
    (inferInstance : (X.subgroupOf (X ⊔ R)).Normal).map _ (QuotientGroup.mk'_surjective _)
  let : ((starImage X R X).subgroupOf (offenderSubgroup (starRepresentation X R))).Normal :=
    inferInstance
  have ht := ExtensionConsequences.DualExtensions.section_generated s hr
    (offenderSubgroup_restrict_eq_top (starRepresentation X R))
  rw [hgen] at ht
  exact (star_thompson_le_offenderSubgroup_from_source h).trans (subgroupOf_eq_top.mp ht)

variable {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The original two-core containment lifts the center placement to NI. -/
theorem normalized_cubic_center_preimage_le_intersection
    (hI : PlaneEscapes Mc ZS I) (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (selection : Normalized H M I X)
    (hz : Nat.card (center (starImage X ((M ⊓ I).pCoreIn 2) X)) = 3)
    (hinner : starImage X ((M ⊓ I).pCoreIn 2) (elementaryAbelianMaxJ ((M ⊓ I).pCoreIn 2)) ≤
      starImage X ((M ⊓ I).pCoreIn 2) X) :
    centralCorePreimage X ≤ M ⊓ I := by
  let h := normalized_component_input (hsource := hsource) hI hcore selection
  have hQ : X.pCoreIn 2 ≤ M ⊓ I := le_inf
    (((pCoreAmbient_mono_of_isSubnormalIn X I 2 selection.component.1
      selection.component.2.subnormal).trans (d.core_le_plane hI)).trans
        (inf_le_left.trans hsource.maximal.1.2))
    ((pCoreIn_le 2 X).trans selection.component.1)
  have hk : pCore 2 X ≤ (M ⊓ I).subgroupOf X :=
    fun x hx => hQ (mem_map_of_mem X.subtype hx)
  rintro z ⟨x,hx,rfl⟩
  have hm := cubic_core_center_le_marked_intersection h hz hinner hx
  have hpre := comap_map_eq_self (f := QuotientGroup.mk' (pCore 2 X))
    (show (QuotientGroup.mk' (pCore 2 X)).ker ≤ (M ⊓ I).subgroupOf X by
      rwa [QuotientGroup.ker_mk'])
  exact (show x ∈ (M ⊓ I).subgroupOf X from hpre ▸ hm)

private theorem residual_intersection_three_dvd
    (hI : PlaneEscapes Mc ZS I) {A : Subgroup G} (hAI : A ≤ I)
    (hKA : (pResidual 2 H).map H.subtype ≤ normalizer (A : Set G))
    (hthree : 3 ∣ Nat.card A) :
    3 ∣ Nat.card ((pResidual 2 H).map H.subtype ⊓ A : Subgroup G) := by
  let K := (pResidual 2 H).map H.subtype
  have hKI : K ≤ I :=
    (le_sup_left.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right
  obtain ⟨E,hE,hcard⟩ := exists_elementaryAbelian_card_primeRank (G := K) (p := 3)
  let := hE
  let EI := E.map (inclusion hKI)
  let e : E ≃* EI := E.equivMapOfInjective (inclusion hKI) (inclusion_injective hKI)
  let : IsElementaryAbelian 3 EI := IsElementaryAbelian.of_injective e.symm.toMonoidHom e.symm.injective
  have hEI : Nat.card EI = 3 ^ 2 := by
    rw [← Nat.card_congr e.toEquiv, hcard, residual_rank_two d]
  have hnorm : EI ≤ normalizer (A.subgroupOf I : Set I) := by
    rw [← subgroupOf_normalizer_eq hAI]
    rintro _ ⟨x,hx,rfl⟩
    exact hKA x.property
  have hAIcard : 3 ∣ Nat.card (A.subgroupOf I) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAI).toEquiv]
    exact hthree
  have hr : primeRank 3 I ≤ 2 :=
    (Chapter1.RadicalExclusions.sqtk_of_mem_H hsource.ambient hI.1).stronglyQuasithin
      3 Nat.prime_three (by decide)
  have hne := Subgroup.inf_ne_bot_of_elementary_plane EI (A.subgroupOf I)
    hnorm hAIcard hEI hr
  have hp : IsPGroup 3 (EI ⊓ A.subgroupOf I : Subgroup I) :=
    (IsElementaryAbelian.isPGroup 3 EI).to_le inf_le_left
  have hd : 3 ∣ Nat.card (EI ⊓ A.subgroupOf I : Subgroup I) := by
    rcases hp.card_eq_or_dvd with h | h
    · exact (hne (card_eq_one.mp h)).elim
    · exact h
  let j : (EI ⊓ A.subgroupOf I : Subgroup I) →* (K ⊓ A : Subgroup G) := {
    toFun := fun x => ⟨x.val.val, by
      obtain ⟨k,hk,he⟩ := x.property.1
      exact ⟨(congrArg Subtype.val he) ▸ k.property,x.property.2⟩⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : (K ⊓ A : Subgroup G) => (z : G)) h
  exact hd.trans (card_dvd_of_injective j hj)

/-- A cubic star center with inner Thompson image contradicts the
original rank-two K and its two-group intersection with M. -/
theorem normalized_component_false_of_cubic_star_center
    (hI : PlaneEscapes Mc ZS I) (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (selection : Normalized H M I X)
    (hz : Nat.card (center (starImage X ((M ⊓ I).pCoreIn 2) X)) = 3)
    (hinner : starImage X ((M ⊓ I).pCoreIn 2) (elementaryAbelianMaxJ ((M ⊓ I).pCoreIn 2)) ≤
      starImage X ((M ⊓ I).pCoreIn 2) X) : False := by
  let h := normalized_component_input (hsource := hsource) hI hcore selection
  let a := cubicCenterCoreStarEquiv h hz
  let C := centralCorePreimage X
  let K := (pResidual 2 H).map H.subtype
  have hCX : C ≤ X := map_subtype_le _
  have hCI : C ≤ I := hCX.trans selection.component.1
  have hKC : K ≤ normalizer (C : Set G) := selection.residual_normalizes.trans
    (normalizer_le_normalizer_characteristic_image X (centralPreimage (pCore 2 X)))
  have hCM : C ≤ M :=
    (normalized_cubic_center_preimage_le_intersection d hI hcore selection hz hinner).trans inf_le_left
  have hthree : 3 ∣ Nat.card C := by
    have hh := (centralPreimage (pCore 2 X)).card_map_dvd (QuotientGroup.mk' (pCore 2 X))
    rw [map_centralPreimage,Nat.card_congr (centerCongr a).toEquiv,hz] at hh
    simpa only [C,centralCorePreimage,card_map_of_injective X.subtype_injective] using hh
  have hd := residual_intersection_three_dvd d hI hCI hKC hthree
  have ht : IsPGroup 2 (K ⊓ C : Subgroup G) := by
    apply (isPGroup_pCoreIn 2 K).to_le
    rw [←residual_intersection_eq_core d]
    exact inf_le_inf_left K hCM
  obtain ⟨k,hk⟩ := ht.exists_card_eq
  rw [hk] at hd
  exact (by norm_num : ¬ (3 : ℕ) ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)

/-- The actual triple-six moved action discharges both center and
Thompson-containment premises of the original-source contradiction. -/
theorem normalized_component_tripleSix_false
    (hI : PlaneEscapes Mc ZS I) (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (selection : Normalized H M I X)
    (hCJ : starImage X ((M ⊓ I).pCoreIn 2) X ≤
      offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))
    (s : MovedSection
      ((starRepresentation X ((M ⊓ I).pCoreIn 2)).comp
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))).subtype)
      ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))))
    (hgen : offenderSubgroup s.action =
      (starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))))
    (ha : ChapterB.SourceInduction.ProjectiveLine.TripleSixAction s.action
      ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))))
    (hr : quadraticRatio s.action = 1) : False := by
  let h := normalized_component_input (hsource := hsource) hI hcore selection
  apply normalized_component_false_of_cubic_star_center d hI hcore selection
  · rw [←Nat.card_congr (centerCongr (subgroupOfEquivOfLe hCJ)).toEquiv,
      Nat.card_congr ha.centerEquiv.toEquiv]
    simp
  · exact ratio_one_thompson_inner_of_generated_component h hCJ s hgen hr

end CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
