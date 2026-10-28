module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.HigherFieldApplications
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Refinement

/-!
# Discharging the original ordinary nonblock premise

The proved rank-one placement theorem applies to the entire original
L(G₁,S), with its literal PSL₂ core quotient. It supplies exactly the
RankOneNonblockContainment contract used by the ordinary refinement.
The actual exceptional residuals therefore exclude higher-field G₂,
triality and Ree, including the central G₂(4) cover. The ordinary
catalogue and subsequent refinement now have no nonblock callback.

Both original primes and the original marker are retained. At prime five
the full Ordinary22 refinement follows; at prime three its independently
owned Rudvalis branch remains. The exchanged consumer uses the same
component. Original 15.1.14 stays explicit for its producer and final
pre-exclusion assembly owner. Small-block reconstruction and general
local-family Borel placement remain with the constrained catalogue owner.

Source: Aschbacher--Smith 15.1.20(2--3), 15.1.21--22, printed pp.1094--1100.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}
/-- The exact full-local-family premise used by the ordinary refinement. -/
theorem rankOneNonblockContainment (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) : d.RankOneNonblockContainment := by
  intro K hK hf hmodel hnot
  obtain ⟨n,hn,hm⟩ := hmodel
  exact d.localFamily_nonshort_PSL2_le_MZ hG hempty hM hJ hu h hK hf hnot n hn hm

variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}

/-- Every exceptional higher-field ordinary row is excluded on the original data. -/
theorem PreExclusionSource.not_exceptional_of_local_source
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) :
    ¬ d.OrdinaryExceptionalHigherField :=
  s.not_exceptional_of_nonblock_containment (h := h) hG hempty hM hJ hu hL
    (d.rankOneNonblockContainment hG hempty hM hJ hu h)

/-- The original Ordinary20 catalogue, with its full nonblock premise discharged. -/
theorem PreExclusionSource.ordinary20_of_local_source
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
    d.Ordinary20Alternatives :=
  s.ordinary20_of_nonblock_containment (h := h) hG hempty hM hJ hu hne hmany hres hL hp
    (d.rankOneNonblockContainment hG hempty hM hJ hu h)

/-- The refined original catalogue retains only the cubic Rudvalis remainder. -/
theorem PreExclusionSource.ordinary22_or_cubic_rudvalis_of_local_source
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
    d.Ordinary22Alternatives ∨ (p = 3 ∧
      Nonempty ((d.L ⧸ pCore 2 d.L) ≃* Rudvalis.Model)) :=
  s.ordinary22_or_cubic_rudvalis_of_source (h := h) hG hempty hM hJ hu hne hmany hres hL hp
    (d.rankOneNonblockContainment hG hempty hM hJ hu h)

/-- At the original prime five, no ordinary refinement premise remains. -/
theorem PreExclusionSource.ordinary22_of_quintic_local_source
    (s : d.PreExclusionSource h.normalized 5)
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
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) : d.Ordinary22Alternatives :=
  s.ordinary22_of_quintic_nonblock_containment (h := h) hG hempty hM hJ hu hne hmany hres hL
    (d.rankOneNonblockContainment hG hempty hM hJ hu h)

/-- The exchanged ordinary exclusion uses the same original component and prime. -/
theorem ExchangedSource.not_ordinary_of_local_source
    (e : d.ExchangedSource) (s : d.PreExclusionSource h.normalized p)
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
    (hp : p = 3 ∨ p = 5) : ¬ IsComponent d.G1 (d.L.subgroupOf d.G1) :=
  e.not_ordinary_of_nonblock_containment (h := h) s hG hempty hM hJ hu hne hmany hres hp
    (d.rankOneNonblockContainment hG hempty hM hJ hu h)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Apply the proved nonblock containment and ordinary refinement to the literal
original marker. Original 15.1.14 remains with its existing producer and final
pre-exclusion assembly owner. Both source primes and the original row are retained. -/
theorem PreparedChosenModule.source_preExclusion_ordinary22_of_local_source
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
      d.PreExclusionSource h.normalized m.prime ∧ d.RankOneNonblockContainment ∧
      (IsComponent d.G1 (d.L.subgroupOf d.G1) →
        d.Ordinary22Alternatives ∨ (m.prime = 3 ∧
          Nonempty ((d.L ⧸ pCore 2 d.L) ≃* Rudvalis.Model))) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,d.rankOneNonblockContainment hG hempty hM hJ hu h,
    fun hL => s.ordinary22_or_cubic_rudvalis_of_local_source (h := h)
      hG hempty hM hJ hu hne hmany hres hL hp⟩
end CFSG.Quasithin.Chapter15.Section01
