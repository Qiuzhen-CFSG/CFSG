module
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.ThompsonCoreCenter
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.ExceptionalSeven
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.AlternatingSix

/-!
# Excluding the natural A₆ row through its original central cover

The inner Thompson image places the full central preimage of X/O₂(X)
in NI. A cubic center would meet the original rank-two residual K
nontrivially, contradicting K intersect M = O₂(K). The core center is
therefore trivial. In the natural A₆ row, ratio one and offender generation
supply that inner Thompson image. The earlier proper Sylow-overgroup
argument forces the same center to have order three, a contradiction.

This excludes the natural A₆ row without a universal MS classification.
The binary symplectic four-space has a different offender subgroup and
ratio; its cubic-cover reconstruction remains a separate obligation.

Source: Aschbacher--Smith original 15.2.23, pp.1116--1117, C.2.7,
pp.145--147, and B.5.1(5), pp.102--103.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
open Section01 PlaneUniquenessPreceding PlaneUniquenessPreceding.LinearThree TerminalLinear
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)

include d in
/-- The original rank-two residual excludes a cubic core-quotient center. -/
theorem normalized_core_center_card_one_of_thompson_inner
    (hI : PlaneEscapes Mc ZS I) (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (s : Normalized H M I X)
    (hi : starImage X ((M ⊓ I).pCoreIn 2) (elementaryAbelianMaxJ ((M ⊓ I).pCoreIn 2)) ≤
      starImage X ((M ⊓ I).pCoreIn 2) X) :
    Nat.card (center (X ⧸ pCore 2 X)) = 1 := by
  let h := normalized_component_input (hsource := hsource) hI hcore s
  rcases coreQuotient_center_card_from_source h with hz | hz
  · exact hz
  let K := (pResidual 2 H).map H.subtype
  let C := centralCorePreimage X
  have hKI : K ≤ I :=
    (le_sup_left.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right
  have hCI : C ≤ I := (map_subtype_le _).trans s.component.1
  have hCM : C ≤ M :=
    (core_center_preimage_le_marked_of_thompson_inner h hi).trans inf_le_left
  have hKC : K ≤ normalizer (C : Set G) := s.residual_normalizes.trans
    (normalizer_le_normalizer_characteristic_image X (centralPreimage (pCore 2 X)))
  have hc : 3 ∣ Nat.card C := by
    have hh := (centralPreimage (pCore 2 X)).card_map_dvd (QuotientGroup.mk' (pCore 2 X))
    rw [map_centralPreimage,hz] at hh
    simpa only [C,centralCorePreimage,card_map_of_injective X.subtype_injective] using hh
  obtain ⟨A,hA,hcard⟩ := exists_elementaryAbelian_card_primeRank (G := K) (p := 3)
  let := hA
  let E := A.map (inclusion hKI)
  let e := A.equivMapOfInjective (inclusion hKI) (inclusion_injective hKI)
  let : IsElementaryAbelian 3 E := IsElementaryAbelian.of_injective e.symm.toMonoidHom e.symm.injective
  have hE : Nat.card E = 3^2 := by
    rw [←Nat.card_congr e.toEquiv,hcard,residual_rank_two d]
  have hn : E ≤ normalizer (C.subgroupOf I : Set I) := by
    rw [←subgroupOf_normalizer_eq hCI]
    rintro _ ⟨x,_,rfl⟩
    exact hKC x.property
  have hne := Subgroup.inf_ne_bot_of_elementary_plane E (C.subgroupOf I) hn
    (by rwa [Nat.card_congr (subgroupOfEquivOfLe hCI).toEquiv]) hE
    ((Chapter1.RadicalExclusions.sqtk_of_mem_H hsource.ambient hI.1).stronglyQuasithin
      3 Nat.prime_three (by decide))
  have htwo : IsPGroup 2 (K ⊓ C : Subgroup G) := by
    apply (isPGroup_pCoreIn 2 K).to_le
    rw [←residual_intersection_eq_core d]
    exact inf_le_inf_left K hCM
  have hle : E ⊓ C.subgroupOf I ≤ (K ⊓ C).subgroupOf I := by
    rintro x ⟨⟨k,_,hk⟩,hx⟩
    have hkx : (k : G) = (x : G) := congrArg Subtype.val hk
    refine ⟨?_,hx⟩
    change (x : G) ∈ K
    rw [←hkx]
    exact k.property
  have hdis := (IsElementaryAbelian.isPGroup 3 E).disjoint_of_coprime htwo.comap_subtype
    (by decide : Nat.Coprime 3 2)
  exact (hne (bot_unique ((le_inf inf_le_left hle).trans hdis.eq_bot.le))).elim


include d in
/-- The natural A₆ action has inner Thompson image, so its cubic core
center cannot occur in the original source geometry. -/
theorem normalized_component_naturalSix_false
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
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
    (e : ActionEquiv (s.action.comp
      ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))).subtype)
      (alternatingNatural 6))
    (hr : quadraticRatio s.action = 1) : False := by
  let h := normalized_component_input (hsource := hsource) hI hcore selection
  have hone := normalized_core_center_card_one_of_thompson_inner d hI hcore selection
    (ratio_one_thompson_inner_of_generated_component h hCJ s hgen hr)
  have hthree := normalized_alternatingSix_core_center_three d horbit hI hcore selection
    ((subgroupOfEquivOfLe hCJ).symm.trans e.groupEquiv)
  omega

end CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
