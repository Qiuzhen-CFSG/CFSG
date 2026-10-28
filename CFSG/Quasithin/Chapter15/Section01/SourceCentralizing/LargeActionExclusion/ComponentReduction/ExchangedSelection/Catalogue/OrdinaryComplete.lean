module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.SourceRows

/-!
# The complete ordinary source rows at the original marker

The ordinary refinement now excludes cubic Rudvalis using a characteristic
subgroup of the original full Sylow group. Apply the independently proved
full-local-family nonblock theorem to remove its last local premise, then
combine the result with the shared parabolic placement on the same component.
Both original primes, the marker, the full module and all quotient conventions
are retained. No degree-four graph-family construction is needed here.

The earlier 15.1.14 residual hypothesis remains explicit. The constrained
rows, including their extra A7/A6/G2 geometric clauses, and final seven-row
assembly remain with the existing catalogue owners. This proves the ordinary
branch of 15.1.22, not the full catalogue or Theorem E.

Source: Aschbacher--Smith 15.1.20--22, printed pp.1094--1100.
-/

public section

open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- The complete ordinary alternatives, with the full-local-family nonblock
premise discharged on the original component at either source prime. -/
theorem PreExclusionSource.source_ordinary22
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
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) (hp : p = 3 ∨ p = 5) :
    d.Ordinary22Alternatives :=
  s.ordinary22_of_source (h := h) hG hempty hM hJ hu hne hmany hres hL hp
    (d.source_rankOneNonblockContainment hG hempty hM hJ hu h)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Construct the original component once and supply shared placement and
the full ordinary catalogue on that same marker and source prime. -/
theorem PreparedChosenModule.source_preExclusion_placement_and_complete_ordinary_rows
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
      (∀ P ∈ d.sourceParabolics, P ≤ M ⊓ d.L ∨ P ≤ d.ML) ∧
      (IsComponent d.G1 (d.L.subgroupOf d.G1) → d.Ordinary22Alternatives) := by
  obtain ⟨d,hZ,hrow,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hrow,s,
    s.source_parabolic_placement (h := h) hG hempty hM hJ hu hne hmany hres hp,
    fun hL => s.source_ordinary22 (h := h)
      hG hempty hM hJ hu hne hmany hres hL hp⟩

end CFSG.Quasithin.Chapter15.Section01
