module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.OriginalSelection
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.ReductionSource
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.RepresentativeBoundSource
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.OriginalTerminal

/-!
# Original rank-two component containment

The selected source data produce the marked four-cover, its Sylow normalizer and the fixed-line representative. The representative centralizer bound builds the global reduction; the literal mixed-centralizer and field-fusion calculations then contradict it. Only the independent earlier source13 is retained.
Source: Aschbacher–Smith, 15.3.35–38, printed pp.1135–1137.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
open ChapterA.Section05To06 LocalCover LocalCover.SourceBorel
variable {G : Type*} [Group G] [Finite G]

/-- Original15.3.38: the rank-two residual lies in every ordinary rank-two
component of an outside overgroup. Original13 is its only earlier-source input. -/
theorem source_lemma_15_3_38_from_selection
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (h13 : ∀ J ∈ d.Hplus, generalizedFitting J ≠ pCore 2 J)
    {I L : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hLI : L ≤ I) (hL : IsComponent I (L.subgroupOf I))
    (hrank : primeRank 3 L = 2) : d.Yplus ≤ L := by
  by_contra hnot
  let s := source_inputs_of_original hG d hempty hM hu hmany h13 hI htwo
  have h : Setup d I L := ⟨hI, hLI, hL, hrank,
    OutsideStructure.rankTwoCase_three_rank hG d hI htwo, hnot⟩
  obtain ⟨r⟩ := local_result s h
  obtain ⟨b⟩ := source_sylow_result s h r
  obtain ⟨v, hv1, hv2, hline, hSv, hSylow⟩ :=
    r.exists_representative_seed hG d hempty hM hu hmany
  have hv : v ∈ r.cover.borel.W₁ := (hline ▸ mem_zpowers v).2
  have hCv := r.representative_centralizer_le_knownSimple hG s h v hv hv1 hv2 hSylow
  obtain ⟨⟨eO⟩, _⟩ := source_mixed_centralizer s h r b
  obtain ⟨R, _, _⟩ := reduction_of_representative hG s h r b v hv1 hv2 hline hSv hCv eO
  exact R.false_of_original hG s h

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
