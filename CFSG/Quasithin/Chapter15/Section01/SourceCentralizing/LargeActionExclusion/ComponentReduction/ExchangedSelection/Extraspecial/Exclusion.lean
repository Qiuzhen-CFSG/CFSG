module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Extraspecial.LinearThreeExclusion
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.OrdinaryApplications

/-!
# Ordinary exclusion for the original extraspecial marker

The original local-family theorem supplies the ordinary catalogue. The
central-preimage residual excludes both its Ordinary22 conclusions and its
separate cubic Rudvalis remainder, so the marked component is not ordinary.
The companion linear-three exclusion eliminates the last constrained
alternative. Catalogue exhaustiveness still belongs to the pre-exclusion
catalogue owner; the exchanged-selection owner retains final assembly.

Source: Aschbacher--Smith 15.1.20--24, printed pp.1094--1101.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterD ChapterD.UniqueFactor Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The proved ordinary refinement and the central residual obstruction
exclude ordinary components, including its cubic Rudvalis remainder. -/
theorem PreExclusionSource.extraspecial_not_ordinary_of_local_source
    {d : CaseIComponentData T M Mc V}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V) (sp : d.PreExclusionSource h.normalized 3)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hex : letI := h.elementary
      SourceCases.Extraspecial (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (c : letI := h.elementary; ExtraspecialMarker.ImageMarking T M V h.normalized)
    (hZ : letI := h.elementary; d.Z1 = ExtraspecialMarker.fixedSubgroup M V h.normalized c.X) :
    ¬ IsComponent d.G1 (d.L.subgroupOf d.G1) := by
  intro hL
  have hn := sp.no_extraspecial_ordinary_postRankOne hG h hex c hZ hL
  rcases sp.ordinary22_or_cubic_rudvalis_of_local_source (h := h)
      hG hempty hM hJ hu hne hmany hres hL (Or.inl rfl) with ha | ⟨_,he⟩
  · exact sp.no_extraspecial_ordinary22 hG h hex c hZ hL ha
  · apply hn
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he))))
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
