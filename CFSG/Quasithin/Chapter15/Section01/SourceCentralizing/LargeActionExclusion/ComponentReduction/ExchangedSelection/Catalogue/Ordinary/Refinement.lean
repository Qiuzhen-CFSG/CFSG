module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.SporadicRefinement.Rudvalis
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.SporadicRefinement.HigmanSims
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Nonsporadic.HigherField.Reduction
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.SporadicRefinement.RudvalisSeed
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.LieParabolics.BinaryRankTwo
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.LieParabolics.Linear.Source

/-!
# Ordinary22 refinement at the original pre-exclusion marker

Exhaust the proved Ordinary20 alternatives at the same component d. The
original Borel and higher-field arguments eliminate the first two rows;
the complete binary rank-two and surviving sporadic refinements supply the
literal Ordinary22 conclusions. The full central-cover HS and Rudvalis
arguments exclude both remaining sporadic branches, completing the ordinary
refinement at both source primes under the retained earlier-source premise.

The source corollary now discharges binary-linear placement using the
parent's published theorem for components normalized by S. The complete
degree-five source family and the direct degree-four flag-reversal argument
retain both proper parabolics, generation and the literal residual identity.
The previous conditional interfaces remain available. The stronger degree-four
graph source-family construction remains with this owner.

RankOneNonblockContainment is still an explicit earlier-source premise,
ranging over the full local family L(G₁,S). Its producer remains
qt-e-1515-constrained-source-catalogue and its final discharge remains with
qt-e-15122-pre-exclusion-catalogue, together with the original residual
premise. The Rudvalis contradiction uses the actual max4 covering and a
nontrivial characteristic subgroup of the original full S; no extra
Rudvalis model or local classification premise remains.
The marker consumers preserve d, Z₁, row, prime and all quotient markings.

Source: Aschbacher--Smith 15.1.20(3), 15.1.21 and ordinary 15.1.22(4)--(7),
printed pp.1094--1100 of refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- Exhaust Ordinary20 at the original marking. Every remaining incomplete
Ordinary22 branch is cubic and has an actual binary-linear, HS or Ru model. -/
theorem PreExclusionSource.ordinary22_or_cubic_linear_hs_ru
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
    (hp : p = 3 ∨ p = 5) (hlocal : d.RankOneNonblockContainment) :
    d.Ordinary22Alternatives ∨ (p = 3 ∧
      ((∃ n : ℕ, (n = 4 ∨ n = 5) ∧
        Nonempty (d.L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))) ∨
       ∃ name : SporadicName, (name = .hs ∨ name = .ru) ∧
        Nonempty ((d.L ⧸ pCore 2 d.L) ≃* name.Carrier))) := by
  have ha := s.ordinary20_of_nonblock_containment (h := h)
    hG hempty hM hJ hu hne hmany hres hL hp hlocal
  cases ha with
  | rankOne hm _ =>
      exact (s.false_of_initial_rankOne (h := h) hG hM hJ hu hne hmany hres hL hp hm).elim
  | higherField hm _ _ =>
      exact (s.false_of_initial_higherField (h := h) hG hempty hM hJ hu hne hmany hres hL hm).elim
  | binaryRankTwo hm _ =>
      exact .inl (s.ordinary22_of_binaryRankTwo (h := h) hp hG hM hJ hu hL hm)
  | sporadic name hn3 hn4 he _ =>
      obtain ⟨e⟩ := he
      rcases s.ordinary22_or_cubic_hs_ru (h := h) hp hG hempty hM hJ hu hL name hn3 hn4 e
          with hr | ⟨hp3,hn⟩
      · exact .inl hr
      · exact .inr ⟨hp3,.inr ⟨name,hn,⟨e⟩⟩⟩
  | linear n hn e _ _ =>
      exact .inr ⟨s.prime_three_of_binaryLinear (h := h) hp hG hM hJ hL hn e,
        .inl ⟨n,hn,⟨e⟩⟩⟩

/-- The full central-cover HS exclusion leaves only cubic binary-linear
and Rudvalis branches in the original ordinary catalogue. -/
theorem PreExclusionSource.ordinary22_or_cubic_linear_ru
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
    (hp : p = 3 ∨ p = 5) (hlocal : d.RankOneNonblockContainment) :
    d.Ordinary22Alternatives ∨ (p = 3 ∧
      ((∃ n : ℕ, (n = 4 ∨ n = 5) ∧
        Nonempty (d.L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))) ∨
       Nonempty ((d.L ⧸ pCore 2 d.L) ≃* Rudvalis.Model))) := by
  rcases s.ordinary22_or_cubic_linear_hs_ru (h := h)
      hG hempty hM hJ hu hne hmany hres hL hp hlocal with ha | ⟨hp3,hm⟩
  · exact .inl ha
  · rcases hm with hl | ⟨name,hn,⟨e⟩⟩
    · exact .inr ⟨hp3,.inl hl⟩
    · rcases hn with rfl | rfl
      · exact (s.not_higmanSims (h := h) hG hempty hM hu hL e).elim
      · exact .inr ⟨hp3,.inr ⟨e⟩⟩

/-- Flag reversal completes every outer-action binary-linear row, leaving
only cubic inner-action binary-linear and Rudvalis branches. -/
theorem PreExclusionSource.ordinary22_or_cubic_inner_linear_ru
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
    (hp : p = 3 ∨ p = 5) (hlocal : d.RankOneNonblockContainment) :
    d.Ordinary22Alternatives ∨ (p = 3 ∧
      ((∃ n : ℕ, (n = 4 ∨ n = 5) ∧
        Nonempty (d.L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) ∧
        d.S ≤ d.L ⊔ centralizer (d.L : Set G)) ∨
       Nonempty ((d.L ⧸ pCore 2 d.L) ≃* Rudvalis.Model))) := by
  rcases s.ordinary22_or_cubic_linear_ru (h := h)
      hG hempty hM hJ hu hne hmany hres hL hp hlocal with ha | ⟨hp3,hm⟩
  · exact .inl ha
  · rcases hm with ⟨n,hn,⟨e⟩⟩ | he
    · rcases s.ordinary22_binaryLinear_or_inner (h := h) hp hG hM hJ hu hL hn e
        with ha | hi
      · exact .inl ha
      · exact .inr ⟨hp3,.inl ⟨n,hn,⟨e⟩,hi⟩⟩
    · exact .inr ⟨hp3,.inr he⟩

/-- Both binary-linear action types are complete under the independently
owned source placement; the only remaining ordinary row is cubic Ru. -/
theorem PreExclusionSource.ordinary22_or_cubic_rudvalis
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
    (hp : p = 3 ∨ p = 5) (hlocal : d.RankOneNonblockContainment)
    (hplacement : ∀ P ∈ d.sourceParabolics, P ≤ M ⊓ d.L ∨ P ≤ d.ML) :
    d.Ordinary22Alternatives ∨ (p = 3 ∧
      Nonempty ((d.L ⧸ pCore 2 d.L) ≃* Rudvalis.Model)) := by
  rcases s.ordinary22_or_cubic_linear_ru (h := h)
      hG hempty hM hJ hu hne hmany hres hL hp hlocal with ha | ⟨hp3,hm⟩
  · exact .inl ha
  · rcases hm with ⟨n,hn,⟨e⟩⟩ | he
    · exact .inl (s.ordinary22_of_binaryLinear (h := h) hp hG hM hJ hu hL hn e hplacement)
    · exact .inr ⟨hp3,he⟩

/-- The published normalizing placement theorem removes the linear-row
placement premise. Only cubic Ru remains, with the independent full
local-family nonblock containment still explicit. -/
theorem PreExclusionSource.ordinary22_or_cubic_rudvalis_of_source
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
    (hp : p = 3 ∨ p = 5) (hlocal : d.RankOneNonblockContainment) :
    d.Ordinary22Alternatives ∨ (p = 3 ∧
      Nonempty ((d.L ⧸ pCore 2 d.L) ≃* Rudvalis.Model)) := by
  rcases s.ordinary22_or_cubic_linear_ru (h := h)
      hG hempty hM hJ hu hne hmany hres hL hp hlocal with ha | ⟨hp3,hm⟩
  · exact .inl ha
  · rcases hm with ⟨n,hn,⟨e⟩⟩ | he
    · exact .inl (s.ordinary22_of_binaryLinear_source (h := h) hp hG hM hJ hu hL hn e)
    · exact .inr ⟨hp3,he⟩

/-- At prime five the original Ordinary22 catalogue follows completely
from the independently owned local-family nonblock containment. -/
theorem PreExclusionSource.ordinary22_of_quintic_nonblock_containment
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
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hlocal : d.RankOneNonblockContainment) :
    d.Ordinary22Alternatives := by
  rcases s.ordinary22_or_cubic_linear_hs_ru (h := h)
      hG hempty hM hJ hu hne hmany hres hL (.inr rfl) hlocal with ha | ⟨he,_⟩
  · exact ha
  · contradiction

/-- All ordinary source 15.1.22 rows at both source primes. The independent
full local-family nonblock premise retains its existing producer and final
catalogue owner; the Rudvalis branch is discharged at the original full S. -/
theorem PreExclusionSource.ordinary22_of_source
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
    (hp : p = 3 ∨ p = 5) (hlocal : d.RankOneNonblockContainment) :
    d.Ordinary22Alternatives := by
  rcases s.ordinary22_or_cubic_rudvalis_of_source (h := h)
      hG hempty hM hJ hu hne hmany hres hL hp hlocal with ha | ⟨_,⟨e⟩⟩
  · exact ha
  · exact (s.not_rudvalis (h := h) hG hempty hM hu hL e).elim

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Apply the actual ordinary exhaustion and refinement at the same original
component, retaining Z₁, row, prime and the full local-family premise. -/
theorem PreparedChosenModule.source_preExclusion_ordinary22_refinement
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
      (IsComponent d.G1 (d.L.subgroupOf d.G1) → d.RankOneNonblockContainment →
        d.Ordinary22Alternatives ∨ (m.prime = 3 ∧
          ((∃ n : ℕ, (n = 4 ∨ n = 5) ∧
            Nonempty (d.L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))) ∨
           ∃ name : ClassificationModels.SporadicName, (name = .hs ∨ name = .ru) ∧
            Nonempty ((d.L ⧸ pCore 2 d.L) ≃* name.Carrier)))) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hL hlocal => s.ordinary22_or_cubic_linear_hs_ru (h := h)
    hG hempty hM hJ hu hne hmany hres hL hp hlocal⟩

/-- Apply the strengthened ordinary refinement after the complete HS
exclusion at the same marker, retaining the independent nonblock premise. -/
theorem PreparedChosenModule.source_preExclusion_ordinary22_without_higmanSims
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
      (IsComponent d.G1 (d.L.subgroupOf d.G1) → d.RankOneNonblockContainment →
        d.Ordinary22Alternatives ∨ (m.prime = 3 ∧
          ((∃ n : ℕ, (n = 4 ∨ n = 5) ∧
            Nonempty (d.L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))) ∨
           Nonempty ((d.L ⧸ pCore 2 d.L) ≃* Rudvalis.Model)))) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hL hlocal => s.ordinary22_or_cubic_linear_ru (h := h)
    hG hempty hM hJ hu hne hmany hres hL hp hlocal⟩

/-- Apply the graph-action refinement at the same original marker. The
remaining binary-linear branch explicitly has inner S-action on L. -/
theorem PreparedChosenModule.source_preExclusion_ordinary22_inner_linear_remainder
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
      (IsComponent d.G1 (d.L.subgroupOf d.G1) → d.RankOneNonblockContainment →
        d.Ordinary22Alternatives ∨ (m.prime = 3 ∧
          ((∃ n : ℕ, (n = 4 ∨ n = 5) ∧
            Nonempty (d.L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) ∧
            d.S ≤ d.L ⊔ centralizer (d.L : Set G)) ∨
           Nonempty ((d.L ⧸ pCore 2 d.L) ≃* Rudvalis.Model)))) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hL hlocal => s.ordinary22_or_cubic_inner_linear_ru (h := h)
    hG hempty hM hJ hu hne hmany hres hL hp hlocal⟩

/-- Apply the full ordinary linear and sporadic refinements at the same
original marker, retaining the independent nonblock and placement inputs. -/
theorem PreparedChosenModule.source_preExclusion_ordinary22_rudvalis_remainder
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
      (IsComponent d.G1 (d.L.subgroupOf d.G1) → d.RankOneNonblockContainment →
        (∀ P ∈ d.sourceParabolics, P ≤ M ⊓ d.L ∨ P ≤ d.ML) →
        d.Ordinary22Alternatives ∨ (m.prime = 3 ∧
          Nonempty ((d.L ⧸ pCore 2 d.L) ≃* Rudvalis.Model))) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hL hlocal hplacement => s.ordinary22_or_cubic_rudvalis (h := h)
    hG hempty hM hJ hu hne hmany hres hL hp hlocal hplacement⟩

/-- Exhaust the ordinary source rows at the same marker, discharging
linear placement by the published normalizing theorem and retaining only
the independent full local-family nonblock premise and cubic Ru branch. -/
theorem PreparedChosenModule.source_preExclusion_ordinary22_rudvalis_remainder_of_source
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
      (IsComponent d.G1 (d.L.subgroupOf d.G1) → d.RankOneNonblockContainment →
        d.Ordinary22Alternatives ∨ (m.prime = 3 ∧
          Nonempty ((d.L ⧸ pCore 2 d.L) ≃* Rudvalis.Model))) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hL hlocal => s.ordinary22_or_cubic_rudvalis_of_source (h := h)
    hG hempty hM hJ hu hne hmany hres hL hp hlocal⟩

/-- Complete ordinary refinement at the same original marker, with its row,
Z₁, source prime and retained covering center. -/
theorem PreparedChosenModule.source_preExclusion_ordinary22
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
      (IsComponent d.G1 (d.L.subgroupOf d.G1) → d.RankOneNonblockContainment →
        d.Ordinary22Alternatives) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hL hlocal => s.ordinary22_of_source (h := h)
    hG hempty hM hJ hu hne hmany hres hL hp hlocal⟩

end CFSG.Quasithin.Chapter15.Section01
