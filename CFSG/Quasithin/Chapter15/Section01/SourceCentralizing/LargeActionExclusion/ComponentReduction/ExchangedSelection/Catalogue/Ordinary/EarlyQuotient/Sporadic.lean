module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.RankOne.Complete
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Sporadic

/-!
# The exhaustive early sporadic catalogue consumer

The complete initial sporadic family feeds the constructor-aware 15.1.21
exclusions immediately, at the same original component and p = 3 or 5.
The later exchanged consumer retains this original pre-exclusion witness.
The remaining Lie-family exhaustion and Ordinary22 refinements stay with
the ordinary pre-exclusion owner.
Source: Aschbacher--Smith 15.1.20(3), 15.1.21, printed pp.1096--1098.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- Every original sporadic marking allowed by 1.1.5 gives the early quotient conclusion with all
initial source clauses discharged. -/
theorem PreExclusionSource.source_ordinary_post_rank_one_model_of_sporadic_quotient
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) (hp : p = 3 ∨ p = 5)
    (name : SporadicName) (not_j3 : name ≠ .j3)
    (model : Nonempty ((d.L ⧸ pCore 2 d.L) ≃* name.Carrier)) :
    OrdinaryPostRankOneModel (d.L ⧸ pCore 2 d.L) := by
  exact (s.ordinary20_of_sporadic_quotient (h := h) hG hempty hM hJ hu hL name not_j3 model).postRankOneModel_of_preExclusion
    (h := h) s hG hM hJ hu hL hp

/-- The same original component and pre-exclusion witness supply the
exhaustive sporadic exchanged-source exclusion. -/
theorem ExchangedSource.not_ordinary_of_preExclusion_sporadic_quotient
    (e : d.ExchangedSource) (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hp : p = 3 ∨ p = 5)
    (name : SporadicName) (not_j3 : name ≠ .j3)
    (model : Nonempty ((d.L ⧸ pCore 2 d.L) ≃* name.Carrier)) :
    ¬ IsComponent d.G1 (d.L.subgroupOf d.G1) := by
  apply e.not_ordinary_of_preExclusion_catalogue (h := h) s hG hM hJ hu hp
  intro hL
  exact s.ordinary20_of_sporadic_quotient (h := h) hG hempty hM hJ hu hL name not_j3 model

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
