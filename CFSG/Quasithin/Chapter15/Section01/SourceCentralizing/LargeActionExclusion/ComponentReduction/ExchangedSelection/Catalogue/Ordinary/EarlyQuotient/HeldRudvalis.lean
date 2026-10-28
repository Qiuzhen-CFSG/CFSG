module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.RankOne.Complete
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Sporadic.HeldRudvalis

/-!
# Early Held and Rudvalis quotients at the original component

The full initial rows, with the actual two-core quotient, central covers and
Sylow-center centralizer clause discharged, feed the constructor-aware
15.1.21 exclusions. Their exchanged-source applications retain the same d
and original pre-exclusion witness. No later selection premise is used to
construct either row.

The remaining initial catalogue and refined 15.1.22 obligations stay with
the ordinary catalogue owner; these are two complete branches.
Source: Aschbacher--Smith 15.1.20(3d), 15.1.21, printed pp.1094--1098.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- The original Held marking gives the early quotient conclusion with all
initial source clauses discharged. -/
theorem PreExclusionSource.source_ordinary_post_rank_one_model_of_held_quotient
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) (hp : p = 3 ∨ p = 5)
    (model : (d.L ⧸ pCore 2 d.L) ≃* Held.He) :
    OrdinaryPostRankOneModel (d.L ⧸ pCore 2 d.L) := by
  exact (s.ordinary20_of_held_quotient (h := h) hG hM hu hL model).postRankOneModel_of_preExclusion
    (h := h) s hG hM hJ hu hL hp

/-- The same original component and pre-exclusion witness supply the
Held exchanged-source exclusion. -/
theorem ExchangedSource.not_ordinary_of_preExclusion_held_quotient
    (e : d.ExchangedSource) (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hp : p = 3 ∨ p = 5)
    (model : (d.L ⧸ pCore 2 d.L) ≃* Held.He) :
    ¬ IsComponent d.G1 (d.L.subgroupOf d.G1) := by
  apply e.not_ordinary_of_preExclusion_catalogue (h := h) s hG hM hJ hu hp
  intro hL
  exact s.ordinary20_of_held_quotient (h := h) hG hM hu hL model

/-- The original Rudvalis marking gives the early quotient conclusion with all
initial source clauses discharged. -/
theorem PreExclusionSource.source_ordinary_post_rank_one_model_of_rudvalis_quotient
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) (hp : p = 3 ∨ p = 5)
    (model : (d.L ⧸ pCore 2 d.L) ≃* Rudvalis.Model) :
    OrdinaryPostRankOneModel (d.L ⧸ pCore 2 d.L) := by
  exact (s.ordinary20_of_rudvalis_quotient (h := h) hG hM hu hL model).postRankOneModel_of_preExclusion
    (h := h) s hG hM hJ hu hL hp

/-- The same original component and pre-exclusion witness supply the
Rudvalis exchanged-source exclusion. -/
theorem ExchangedSource.not_ordinary_of_preExclusion_rudvalis_quotient
    (e : d.ExchangedSource) (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hp : p = 3 ∨ p = 5)
    (model : (d.L ⧸ pCore 2 d.L) ≃* Rudvalis.Model) :
    ¬ IsComponent d.G1 (d.L.subgroupOf d.G1) := by
  apply e.not_ordinary_of_preExclusion_catalogue (h := h) s hG hM hJ hu hp
  intro hL
  exact s.ordinary20_of_rudvalis_quotient (h := h) hG hM hu hL model

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
