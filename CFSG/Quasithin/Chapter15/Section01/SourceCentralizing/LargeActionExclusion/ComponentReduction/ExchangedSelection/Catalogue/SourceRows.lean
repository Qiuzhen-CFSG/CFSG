module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.FixedPairPlacement.SourceAssembly
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Refinement

/-!
# Applying shared source geometry to the ordinary catalogue rows

The complete shared pair placement and the full-local-family nonblock
proof discharge both extra inputs of the actual Ordinary22 consumer.
The resulting ordinary refinement has only the cubic Rudvalis remainder;
at prime five it supplies all four ordinary source alternatives. The
original-marker application retains the same component and prime.

The remaining cubic Rudvalis proof belongs to
qt-e-15122-ordinary-pre-exclusion, and the constrained source rows to
qt-e-1515-constrained-source-catalogue. This catalogue owner retains
assembly of all seven rows, including the extra A₇ weight-two stabilizer
and A₆/G₂ parabolic clauses. Those statements are not replaced by the
weaker ConstrainedAlternatives interface.

Source: Aschbacher--Smith 15.1.22(4)--(7), printed pp.1098--1100.
-/

public section

open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- Apply the full shared placement and local-family proofs to the actual
ordinary 15.1.22 row consumer. Only the independently owned cubic Rudvalis
exclusion remains in the ordinary source refinement. -/
theorem PreExclusionSource.source_ordinary22_or_cubic_rudvalis
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
  s.ordinary22_or_cubic_rudvalis (h := h) hG hempty hM hJ hu hne hmany hres hL hp
    (d.source_rankOneNonblockContainment hG hempty hM hJ hu h)
    (s.source_parabolic_placement (h := h) hG hempty hM hJ hu hne hmany hres hp)

/-- The prime-five ordinary source rows have no remaining local-family or
placement premise. The original earlier residual is still retained. -/
theorem PreExclusionSource.source_ordinary22_quintic
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
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) : d.Ordinary22Alternatives := by
  rcases s.source_ordinary22_or_cubic_rudvalis (h := h)
      hG hempty hM hJ hu hne hmany hres hL (.inr rfl) with ha | ⟨hf,_⟩
  · exact ha
  · contradiction

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The same original marker supplies shared placement and the ordinary
row refinement, without an unexplained nonblock or normalization premise. -/
theorem PreparedChosenModule.source_preExclusion_placement_and_ordinary_rows
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
      (IsComponent d.G1 (d.L.subgroupOf d.G1) →
        d.Ordinary22Alternatives ∨ (m.prime = 3 ∧
          Nonempty ((d.L ⧸ pCore 2 d.L) ≃* Rudvalis.Model))) := by
  obtain ⟨d,hZ,hrow,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hrow,s,
    s.source_parabolic_placement (h := h) hG hempty hM hJ hu hne hmany hres hp,
    fun hL => s.source_ordinary22_or_cubic_rudvalis (h := h)
      hG hempty hM hJ hu hne hmany hres hL hp⟩

end CFSG.Quasithin.Chapter15.Section01
