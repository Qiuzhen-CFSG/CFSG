module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.RankOne.Complete
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Sporadic.JankoFour

/-!
# The early catalogue consumers for the excluded J₄ marking

The original pre-exclusion source rules out the actual J₄ two-core quotient,
including central covers. Its Ordinary20 branch immediately feeds the
constructor-aware post-rank-one catalogue and the same-component exchanged
consumer. No later selection hypothesis is used in the source exclusion.
Source: Aschbacher--Smith 15.1.20(3), 15.1.21, printed pp.1097--1098.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- The original J₄ marking gives the early quotient conclusion with all
initial source clauses discharged. -/
theorem PreExclusionSource.source_ordinary_post_rank_one_model_of_jankoFour_quotient
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) (hp : p = 3 ∨ p = 5)
    (model : (d.L ⧸ pCore 2 d.L) ≃* Janko4.Model) :
    OrdinaryPostRankOneModel (d.L ⧸ pCore 2 d.L) := by
  exact (s.ordinary20_of_jankoFour_quotient (h := h) hG hempty hM hJ hu hL model).postRankOneModel_of_preExclusion
    (h := h) s hG hM hJ hu hL hp

/-- The same original component and pre-exclusion witness supply the
J₄ exchanged-source exclusion. -/
theorem ExchangedSource.not_ordinary_of_preExclusion_jankoFour_quotient
    (e : d.ExchangedSource) (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hp : p = 3 ∨ p = 5)
    (model : (d.L ⧸ pCore 2 d.L) ≃* Janko4.Model) :
    ¬ IsComponent d.G1 (d.L.subgroupOf d.G1) := by
  apply e.not_ordinary_of_preExclusion_catalogue (h := h) s hG hM hJ hu hp
  intro hL
  exact s.ordinary20_of_jankoFour_quotient (h := h) hG hempty hM hJ hu hL model

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
