module
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl.Selected
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.OriginalSource

/-!
# The selected-source versions of original15.3.11--12

The actual natural orthogonal action forces |Z|=2. The full14.1.12 source
therefore identifies the original ordering maximum with its selected local,
proving both M!=Mc and N_G(Baum(T))<=M. These literal consumers remove the
last two preceding selection premises from the earlier15.3.11--12 source
assemblies while preserving all their public interfaces.

The original local data and15.3.10 choice remain the standing source setup.
The component inner-splitting endpoint retains the proof's precise three-part
orders, separately from the printed stronger full-order assertion.
Source: Aschbacher--Smith14.1.12 and15.3.10--12, pp.978--979,1123--1125.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03
open ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

namespace OutsideStructure
/-- All twelve15.3.11 clauses, with original14.1.12 selection discharged. -/
theorem source_lemma_15_3_11_from_selection
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (I : Subgroup G) (hI : I ∈ d.Hplus) : Conclusions d I := by
  obtain ⟨hne,hBaum,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  exact source_lemma_15_3_11 hG d hempty hM hu hmany hne hBaum I hI
end OutsideStructure

namespace ComponentIntersection
theorem source_lemma_15_3_12_1_from_selection
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I L : Subgroup G} (hI : I ∈ d.Hplus) (hLI : L ≤ I)
    (hL : (L.subgroupOf I).IsCComponent)
    (hYrank : primeRank 3 d.Yplus = 2) (hLrank : 1 ≤ primeRank 3 L) :
    intersectionResidual d.Yplus L ≠ ⊥ ∧ d.R ≤ normalizer (L : Set G) ∧
      (L.pCoreIn 2 : Set G) * ((intersectionResidual d.Yplus L).pCoreIn 2 : Set G) ⊆
        (d.R : Set G) := by
  obtain ⟨hne,hBaum,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  exact source_lemma_15_3_12_1 hG d hempty hM hu hmany hne hBaum hI hLI hL hYrank hLrank

theorem source_lemma_15_3_12_2_three_parts_from_selection
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I L : Subgroup G} (hI : I ∈ d.Hplus) (hLI : L ≤ I)
    (hL : (L.subgroupOf I).IsCComponent)
    (hYrank : primeRank 3 d.Yplus = 2) (hLrank : primeRank 3 L = 1)
    (hinner : InducesInnerOnTwoCoreQuotient d.Yplus L) :
    (d.Yplus : Set G) = (intersectionResidual d.Yplus L : Set G) *
        (centralizerResidual d.Yplus L : Set G) ∧
      IsPGroup 2 (intersectionResidual d.Yplus L ⊓ centralizerResidual d.Yplus L : Subgroup G) ∧
      Nat.card (TwoCoreQuotient d.Yplus) = 9 ∧
      Nat.card (TwoCoreQuotient (centralizerResidual d.Yplus L)) = 3 ∧
      Nonempty (TwoCoreQuotient d.Yplus ≃* ElementaryNine) ∧
      3 ^ (Nat.card (intersectionResidual d.Yplus L)).factorization 3 = 3 ∧
      3 ^ (Nat.card (centralizerResidual d.Yplus L)).factorization 3 = 3 := by
  obtain ⟨hne,hBaum,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  exact source_lemma_15_3_12_2_three_parts hG d hempty hM hu hmany hne hBaum hI hLI hL hYrank hLrank hinner

end ComponentIntersection
end CFSG.Quasithin.Chapter15.Section03
