module
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.OriginalSource
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.SourceSQTK
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.SourceQuotients
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.OddRank
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.InnerSplitting
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceModels

/-!
# The original component-intersection source application

The complete original15.3.11 supplies the actual Sylow subgroup, theta
identity and quotient alternatives. The actual outside subgroup is SQTK,
as is its two-core quotient. Thus the genuine A.3.7 and full1.2.1(3) sources
supply both commutator inclusions and the component orbit/model facts.
This proves the nontrivial intersection residual, its core product bound,
and normalization of the original component by R.

For three-rank-one components with the source inner-action hypothesis,
the intersection quotient has order3. The complete rank-two branch of
15.3.11 then supplies the inner splitting, actual E₉ quotient and both
three-parts. All earlier local and component callbacks are discharged.
The three-part assertion matches the printed proof and downstream15.3.18;
it is kept distinct from the stronger full-order assertion in15.3.12's
printed statement, whose local obstruction is proved in Basic.

Source: Aschbacher--Smith15.3.12, printed pp.1124--1125.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.ComponentIntersection
open ChapterA.Section05To06 Chapter1.Section02 OutsideStructure
variable {G : Type*} [Group G] [Finite G]

/-- Original15.3.12(1), with every earlier local and component source instantiated. -/
theorem source_lemma_15_3_12_1
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hne : d.Mc ≠ d.M)
    (hBaum : normalizer (ChapterB.baumann (d.T : Subgroup G) : Set G) ≤ d.M)
    {I L : Subgroup G} (hI : I ∈ d.Hplus) (hLI : L ≤ I)
    (hL : (L.subgroupOf I).IsCComponent)
    (hYrank : primeRank 3 d.Yplus = 2) (hLrank : 1 ≤ primeRank 3 L) :
    intersectionResidual d.Yplus L ≠ ⊥ ∧ d.R ≤ normalizer (L : Set G) ∧
      (L.pCoreIn 2 : Set G) * ((intersectionResidual d.Yplus L).pCoreIn 2 : Set G) ⊆
        (d.R : Set G) := by
  have h11 := source_lemma_15_3_11 hG d hempty hM hu hmany hne hBaum I hI
  obtain ⟨P,hP⟩ := h11.sylow
  have hQ := outside_twoCoreQuotient_sqtk hG d hI
  exact odd_rank_component_intersection_of_local_facts hI
    (inf_le_left.trans d.sylow_le) h11.theta_eq.symm hLI hL P hP
    (fun K hK hneK => proposition_1_2_1_two_of_A_3_7
      ChapterA.Section03.CComponentCommutation.universal_A_3_7 hQ hL hK hneK.symm)
    (proposition_1_2_1_three_index_knownSimple hQ hL) hYrank hLrank
    ((outside_sqtk hG d hI).stronglyQuasithin 3 (by decide) (by decide))

/-- The inner-action part of15.3.12(2), with the proof's precise three-part orders. -/
theorem source_lemma_15_3_12_2_three_parts
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hne : d.Mc ≠ d.M)
    (hBaum : normalizer (ChapterB.baumann (d.T : Subgroup G) : Set G) ≤ d.M)
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
  have h11 := source_lemma_15_3_11 hG d hempty hM hu hmany hne hBaum I hI
  have htwo := rank_two_case_of_three_rank_two d I h11.local_structure hYrank
  obtain ⟨hq,he,halt⟩ := cubic_quotient_facts d.Yplus htwo.1
  obtain ⟨P,hP⟩ := h11.sylow
  have hQ := outside_twoCoreQuotient_sqtk hG d hI
  obtain ⟨hYne,_,_,hcard,_⟩ := rank_one_component_intersection_of_local_facts hI
    (inf_le_left.trans d.sylow_le) h11.theta_eq.symm hLI hL P hP
    (fun K hK hneK => proposition_1_2_1_two_of_A_3_7
      ChapterA.Section03.CComponentCommutation.universal_A_3_7 hQ hL hK hneK.symm)
    (proposition_1_2_1_three_index_knownSimple hQ hL) hYrank hLrank
    ((outside_sqtk hG d hI).stronglyQuasithin 3 (by decide) (by decide)) hq he
  exact inner_splitting_of_preliminary_facts d.choice hI hLI hL hLrank hYrank hinner
    hYne hcard h11.theta_eq.symm halt he

end CFSG.Quasithin.Chapter15.Section03.ComponentIntersection
