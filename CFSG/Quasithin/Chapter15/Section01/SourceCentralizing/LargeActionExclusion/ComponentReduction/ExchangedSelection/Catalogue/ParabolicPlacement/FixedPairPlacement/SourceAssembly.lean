module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.FixedPairPlacement.Normalizer
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.FixedPairPlacement.ConstrainedBaumann
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.FixedPairPlacement.OrdinarySource
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.HigherFieldApplications
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Nonsporadic.HigherField.Reduction

/-!
# Original source placement and escaping-family centralizers

Baumann normalization proves (*) in the entire constrained branch. The
independently proved full-local-family PSL₂ nonblock theorem discharges
the precise earlier premise of the ordinary catalogue, so its existing
rank argument proves (*) in the ordinary branch. Both use one universal
characteristic pair before choosing a parabolic.

The original plus geometry then supplies (!), with only its stated
order-two omega-center and escaping-family hypotheses. The marker
application preserves d, Z₁, row, and either source prime. Original
15.1.14 remains an explicit earlier input, produced by
qt-e-1514-global-thompson-residual and discharged by the final assembly.
The complete seven-row catalogue still requires the independent ordinary
and constrained model/parabolic constructions; no row exhaustion is
asserted here.

Source: Aschbacher--Smith 15.1.20--22, printed pp.1094--1100.
-/

public section

open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- Original (*) for every constrained component, including components moved
by S and literal symmetric-three parabolic quotients. -/
theorem PreExclusionSource.parabolic_placement_of_constrained
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L) :
    ∀ P ∈ d.sourceParabolics, P ≤ M ⊓ d.L ∨ P ≤ d.ML :=
  s.parabolic_placement_of_baumann_normalizes hG hM hJ hu h
    (d.localFamily_baumann_normalizes hG hempty hM hJ hu h
      ⟨d.L_component.1,s.local_component⟩ s.quasisimple d.L_not_le_MZ hf)

/-- The independently proved PSL₂ nonblock theorem supplies the exact
full-local-family premise of the ordinary catalogue. -/
theorem source_rankOneNonblockContainment (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) : d.RankOneNonblockContainment := by
  intro K hK hf hq hn
  obtain ⟨n,hnn,hq⟩ := hq
  exact d.localFamily_nonshort_PSL2_le_MZ hG hempty hM hJ hu h hK hf hn n hnn hq

/-- Discharge the earlier ordinary catalogue's only local-family premise
using its independently proved constrained nonblock producer. The genuine
15.1.14 residual remains explicit for the final source assembly. -/
theorem PreExclusionSource.source_ordinary20
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
    (d.source_rankOneNonblockContainment hG hempty hM hJ hu h)

/-- Original 15.1.22(*), with both component branches and both source
primes. There is no component-normalization, model or pair callback. -/
theorem PreExclusionSource.source_parabolic_placement
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
    (hp : p = 3 ∨ p = 5) :
    ∀ P ∈ d.sourceParabolics, P ≤ M ⊓ d.L ∨ P ≤ d.ML := by
  rcases d.L_component.2.component_or_generalizedFitting_eq_pCore s.odd_core with hc | hf
  · exact s.parabolic_placement_of_ordinary20 (h := h) hG hM hJ hu hc hp
      (s.source_ordinary20 (h := h) hG hempty hM hJ hu hne hmany hres hc hp)
  · have hfL : generalizedFitting d.L = pCore 2 d.L := by
      let e : d.L.subgroupOf d.G1 ≃* d.L := subgroupOfEquivOfLe d.L_component.1
      exact (map_generalizedFitting_equiv e).symm.trans
        ((congrArg (Subgroup.map e.toMonoidHom) hf).trans (pCore_map_iso 2 e))
    exact s.parabolic_placement_of_constrained (h := h) hG hempty hM hJ hu hfL

/-- Original (!) with the same-pair placement and plus geometry discharged.
The order-two omega-center and escaping family are its stated source premises. -/
theorem PreExclusionSource.source_parabolic_family_centralizer
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hfull : V = localModule T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hp : p = 3 ∨ p = 5) (hcard : Nat.card d.plusOmega = 2)
    (F : Set (Subgroup G)) (hF : F ⊆ d.sourceParabolics) (hout : ¬ sSup F ≤ d.ML) :
    (∀ P ∈ F, ¬ P ≤ d.ML → P ≤ M) ∧
      (¬ d.localThreeResidual ≤ d.ML) ∧
      d.S ⊓ centralizer (d.localThreeResidual : Set G) =
        d.S ⊓ centralizer (d.L : Set G) :=
  s.parabolic_family_centralizer_of_placement (h := h) hG hfull hM.1.2 hu
    (s.source_parabolic_placement (h := h) hG hempty hM hJ hu hne hmany hres hp)
    hcard F hF hout

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The actual original marker supplies (*) and (!) for both primes and
both component branches, retaining only the genuine earlier residual input.
The model-specific family construction and full seven-row assembly remain
with this catalogue and its independently owned ordinary/constrained inputs. -/
theorem PreparedChosenModule.source_preExclusion_parabolic_placement
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
      ∀ (F : Set (Subgroup G)), F ⊆ d.sourceParabolics → ¬ sSup F ≤ d.ML →
        Nat.card d.plusOmega = 2 →
        (∀ P ∈ F, ¬ P ≤ d.ML → P ≤ M) ∧
          (¬ d.localThreeResidual ≤ d.ML) ∧
          d.S ⊓ centralizer (d.localThreeResidual : Set G) =
            d.S ⊓ centralizer (d.L : Set G) := by
  obtain ⟨d,hZ,hrow,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hrow,s,?_,?_⟩
  · exact s.source_parabolic_placement (h := h) hG hempty hM hJ hu hne hmany hres hp
  · intro F hF hout hcard
    exact s.source_parabolic_family_centralizer
      (h := h) hG hempty hM hJ hfull hu hne hmany hres hp hcard F hF hout

end CFSG.Quasithin.Chapter15.Section01
