module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.OrdinaryApplications

/-!
# The complete ordinary catalogue from the original local hypotheses

Combine the complete ordinary refinement, including the full-S Rudvalis
characteristic-subgroup exclusion, with the proved full-local-family
nonblock theorem. This discharges the last nonblock callback for both
source primes. The earlier Ordinary20 catalogue also supplies the literal
post-rank-one quotient consumed by ordinary elimination.

The marker application supplies all three conclusions on the same d,
retaining Z₁, row, prime, central covers and the original pre-selection
hypotheses. Original 15.1.14 remains an explicit earlier-source input,
with final discharge owned by qt-e-15122-pre-exclusion-catalogue. The
separate degree-four graph-family obligation is not used here.

Source: Aschbacher--Smith 15.1.20(3), 15.1.21 and 15.1.22(4)--(7),
printed pp.1094--1100 of refs/quasithin.pdf.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- All ordinary 15.1.22 rows, with the full-local-family premise discharged. -/
theorem PreExclusionSource.ordinary22_of_local_source
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hp : p = 3 ∨ p = 5) :
    d.Ordinary22Alternatives :=
  s.ordinary22_of_source (h := h) hG hempty hM hJ hu hne hmany hres hL hp
    (d.rankOneNonblockContainment hG hempty hM hJ hu h)

/-- The literal early quotient catalogue used by ordinary elimination. -/
theorem PreExclusionSource.postRankOneModel_of_local_source
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hp : p = 3 ∨ p = 5) :
    OrdinaryPostRankOneModel (d.L ⧸ pCore 2 d.L) :=
  (s.ordinary20_of_local_source (h := h) hG hempty hM hJ hu hne hmany hres hL hp).postRankOneModel_of_preExclusion (h := h) s hG hM hJ hu hL hp

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The full initial and refined ordinary catalogues, and their early quotient
consumer, at one unchanged original marker. No nonblock callback remains. -/
theorem PreparedChosenModule.source_preExclusion_ordinary_catalogues
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized) (hp : m.prime = 3 ∨ m.prime = 5)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (IsComponent d.G1 (d.L.subgroupOf d.G1) →
        d.Ordinary20Alternatives ∧ d.Ordinary22Alternatives ∧
          CaseIComponentData.OrdinaryPostRankOneModel (d.L ⧸ pCore 2 d.L)) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,fun hL => ?_⟩
  have h20 := s.ordinary20_of_local_source (h := h)
    hG hempty hM hJ hu hne hmany hres hL hp
  exact ⟨h20,s.ordinary22_of_local_source (h := h)
    hG hempty hM hJ hu hne hmany hres hL hp,
    h20.postRankOneModel_of_preExclusion (h := h) s hG hM hJ hu hL hp⟩

end CFSG.Quasithin.Chapter15.Section01
