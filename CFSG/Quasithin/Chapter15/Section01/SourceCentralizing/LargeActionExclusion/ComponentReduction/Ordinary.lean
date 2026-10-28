module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Ordinary.Catalogue
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Ordinary.Triality
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Ordinary.Held
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Ordinary.Rudvalis

/-!
# Ordinary terminal-model elimination on the same exchanged component

Every model in source 15.1.20(3c--e) contradicts the fixed-plane centralizer
obstruction. All model facts are discharged, including Held, Rudvalis and
the genuine triality carrier. The argument applies to both plane sizes.

The actual Nine selection supplies a component to these exclusions. Final
ordinary-component elimination is conditional on deriving the displayed
post-rank-one catalogue from the source hypotheses; that derivation requires
15.1.20--21 and is not proved by this module. The conditional consumer makes
the remaining obligation explicit and then applies ordinary_or_constrained.

Source: Aschbacher--Smith 15.1.20--22, 15.1.25--26, printed pp.1094--1102.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- All ordinary terminal models are excluded on this same source component.
The earlier source catalogue is not assumed here. -/
theorem ExchangedSource.not_ordinary_post_rank_one_model {d : CaseIComponentData T M Mc V}
    (s : d.ExchangedSource) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) :
    ¬ OrdinaryPostRankOneModel (d.L ⧸ pCore 2 d.L) := by
  obtain ⟨hs, hb⟩ := s.not_ordinary_small_models hG hM hu h hL
  rintro (hm | hm | hm | hm | hm | hm)
  · exact hs hm
  · exact hb hm
  · exact s.not_ordinary_hs hG hM hu h hL hm
  · exact s.not_ordinary_held hG hM hu h hL hm
  · exact s.not_ordinary_rudvalis hG hM hu h hL hm
  · exact s.not_ordinary_triality hG hM hu h hL hm

/-- Conditional final assembly: the earlier catalogue must still be proved
from source 15.1.20--21. All exclusions of its terminal models are discharged. -/
theorem ExchangedSource.not_ordinary_of_post_rank_one_catalogue
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hcatalogue : IsComponent d.G1 (d.L.subgroupOf d.G1) →
      OrdinaryPostRankOneModel (d.L ⧸ pCore 2 d.L)) :
    ¬ IsComponent d.G1 (d.L.subgroupOf d.G1) := by
  intro hL
  exact s.not_ordinary_post_rank_one_model hG hM hu h hL (hcatalogue hL)

end CaseIComponentData

/-- The actual Nine selection carries all terminal ordinary-model exclusions,
without any catalogue, model-fact or marked-action premise. -/
theorem PreparedChosenModule.source_caseI_nine_ordinary_terminal_exclusions
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (h9 : letI := h.elementary
      SourceCases.Nine (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.ExchangedSource ∧
      (IsComponent d.G1 (d.L.subgroupOf d.G1) →
        ¬ CaseIComponentData.OrdinaryPostRankOneModel (d.L ⧸ pCore 2 d.L)) := by
  obtain ⟨d, s⟩ := h.source_caseI_nine_exchanged_source hG T hempty hM hmany hJ hu hne
    hfull h9 hres
  exact ⟨d, s, s.not_ordinary_post_rank_one_model hG hM hu h⟩

/-- Apply the conditional ordinary elimination to an actual Nine selection.
Only the earlier post-rank-one source catalogue remains beyond the authorized
15.1.14 residual hypothesis. This is not an unconditional proof of 15.1.26. -/
theorem PreparedChosenModule.source_caseI_nine_constrained_of_ordinary_catalogue
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (h9 : letI := h.elementary
      SourceCases.Nine (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hcatalogue : ∀ d : CaseIComponentData T M Mc V, d.ExchangedSource →
      IsComponent d.G1 (d.L.subgroupOf d.G1) →
        CaseIComponentData.OrdinaryPostRankOneModel (d.L ⧸ pCore 2 d.L)) :
    ∃ d : CaseIComponentData T M Mc V, d.ExchangedSource ∧
      generalizedFitting d.L = pCore 2 d.L := by
  obtain ⟨d, s⟩ := h.source_caseI_nine_exchanged_source hG T hempty hM hmany hJ hu hne
    hfull h9 hres
  refine ⟨d, s, (d.ordinary_or_constrained s.odd_core).resolve_left ?_⟩
  exact s.not_ordinary_of_post_rank_one_catalogue hG hM hu h (hcatalogue d s)

end CFSG.Quasithin.Chapter15.Section01
