module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.RankOne.Complete
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Sporadic.HigmanSims

/-!
# The early Higman--Sims quotient at the original component

The complete initial row, with the actual two-core quotient, central covers,
and Sylow-center centralizer identity, feeds the constructor-aware 15.1.21
exclusions. The exchanged-source application retains the same d and the
original pre-exclusion witness. No later selection premise constructs the row.
The remaining initial catalogue and refined 15.1.22 obligations stay with the
ordinary catalogue owner.
Source: Aschbacher--Smith 15.1.20(3d), 15.1.21, printed pp.1096--1098.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- The original Higman--Sims marking gives the early quotient conclusion with all
initial source clauses discharged. -/
theorem PreExclusionSource.source_ordinary_post_rank_one_model_of_higmanSims_quotient
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) (hp : p = 3 ∨ p = 5)
    (model : (d.L ⧸ pCore 2 d.L) ≃* Sporadic.LeechRelated.HS.Carrier) :
    OrdinaryPostRankOneModel (d.L ⧸ pCore 2 d.L) := by
  exact (s.ordinary20_of_higmanSims_quotient (h := h) hG hM hu hL model).postRankOneModel_of_preExclusion
    (h := h) s hG hM hJ hu hL hp

/-- The same original component and pre-exclusion witness supply the
Higman--Sims exchanged-source exclusion. -/
theorem ExchangedSource.not_ordinary_of_preExclusion_higmanSims_quotient
    (e : d.ExchangedSource) (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hp : p = 3 ∨ p = 5)
    (model : (d.L ⧸ pCore 2 d.L) ≃* Sporadic.LeechRelated.HS.Carrier) :
    ¬ IsComponent d.G1 (d.L.subgroupOf d.G1) := by
  apply e.not_ordinary_of_preExclusion_catalogue (h := h) s hG hM hJ hu hp
  intro hL
  exact s.ordinary20_of_higmanSims_quotient (h := h) hG hM hu hL model

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
