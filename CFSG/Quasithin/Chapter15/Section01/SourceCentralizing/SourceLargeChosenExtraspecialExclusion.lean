module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceLargeChosenCatalogue
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Extraspecial

/-!
# Exclusion of the original full extraspecial source after 15.1.14

The original extraspecial action constructs its literal marker and selected
component. Its checked exclusions rule out both ordinary component status
and the constrained alternatives. The proved actual-source catalogue supplies
their disjunction on that same component, completing the row contradiction.

The only earlier conclusion assumed is the permitted residual statement of
15.1.14. There is no catalogue, model, or reconstruction callback.
Source: Aschbacher--Smith 15.1.15--26, printed pp.1091--1102.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original full extraspecial action is impossible once the earlier
15.1.14 residual statement is available. -/
theorem PreparedChosenModule.false_of_full_extraspecial_after_residual
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (hex : letI := h.elementary
      SourceCases.Extraspecial (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) : False := by
  let := h.elementary
  obtain ⟨_,_,d,_,_,_,_,_,_,_,_,_,_,s,hordinary,hconstrained⟩ :=
    h.source_extraspecial_catalogue_obstruction
      hG T hempty hM hmany hJ hu hne hfull hex hres
  exact (s.original_component_or_constrained_catalogue (h := h)
    hG hempty hM hJ hu hne hmany hfull hres).elim hordinary hconstrained

end CFSG.Quasithin.Chapter15.Section01
