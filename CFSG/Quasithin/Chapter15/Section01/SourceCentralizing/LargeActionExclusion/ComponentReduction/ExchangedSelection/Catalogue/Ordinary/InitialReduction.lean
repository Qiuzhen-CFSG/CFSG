module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.EarlyQuotient.Alternating
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.EarlyQuotient.OddCharacteristic
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.EarlyQuotient.HigherField
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.EarlyQuotient.Linear
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.EarlyQuotient.BinaryRankTwo
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.EarlyQuotient.Sporadic
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived

/-!
# Exhaustion up to the exceptional higher-field models

The six actual model/action alternatives of 1.1.5 are exhausted at the
original fixed component. The proved initial rows and exclusions leave
only higher-field G₂, triality, Ree, and the retained central two-covers of
G₂(4) outside the full Ordinary20 conclusion. The small linear and derived
symplectic endpoints are transported through actual model isomorphisms;
the field-order marking identifies the binary triality endpoint exactly.

The early quotient and later exchanged consumers use the same d and the
same pre-exclusion witness. No exceptional exclusion is assumed here.
These remaining exclusions and the Ordinary22 refinements stay with
qt-e-15122-ordinary-pre-exclusion. The source route for exceptional
parabolic residuals needs the full local-family theorem from
qt-e-1515-constrained-source-catalogue, which is not discharged by the
ambient-component restriction. Original 15.1.14 remains with
qt-e-1514-global-thompson-residual and final source assembly in
qt-e-15122-pre-exclusion-catalogue.
Source: Aschbacher--Smith 15.1.20(3), printed pp.1094--1097, and
15.1.21, printed pp.1097--1098.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
open Chapter1.Section02.LocalModels Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- The exact remaining model branches, not an asserted exclusion or a source catalogue. -/
inductive OrdinaryExceptionalHigherField (d : CaseIComponentData T M Mc V) : Prop
  | g2 (n : ℕ) (degree : 1 < n) (model : IsG2At d.L (2^n))
  | triality (n : ℕ) (degree : 1 < n)
      (model : Triality.Standard.IsTrialityGroupAt (2^n) d.L)
  | ree (m : ℕ) (degree : 1 ≤ m) (model : IsReeF4At d.L m)
  | g2_cover (nontrivial_center : center d.L ≠ ⊥)
      (model : IsG2At (d.L ⧸ pCore 2 d.L) 4)

/-- The rank-two 1.1.5 family reduces to proved initial rows or the three exceptional families. -/
theorem PreExclusionSource.ordinary20_or_exceptional_of_rankTwo
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
    (hm : RankTwoTheoremC d.L) :
    d.Ordinary20Alternatives ∨ d.OrdinaryExceptionalHigherField := by
  cases hm with
  | linear n hn hm =>
      by_cases hn1 : n = 1
      · subst n
        obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
        let := Fintype.ofFinite F
        let k : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
          simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod,pow_one] using hF)
        exact (s.false_of_pslThreeTwo_equiv (h := h) hG hM hu hmany hres hL
          (e.trans (Atlas.fieldEquivPSL 3 k))).elim
      · exact .inl (s.ordinary20_of_higherField (h := h) hG hempty hM hJ hu hne hmany hres hL
          (.inl ⟨n,by omega,.inl hm⟩))
  | symplectic n hn hm =>
      exact .inl (s.ordinary20_of_higherField (h := h) hG hempty hM hJ hu hne hmany hres hL
        (.inl ⟨n,by omega,.inr hm⟩))
  | g2 n hn hm => exact .inr (.g2 n (by omega) hm)
  | triality n hn hm =>
      by_cases hn1 : n = 1
      · subst n
        obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_two_iff d.L).mp
          (by simpa only [pow_one] using hm)
        exact .inl (s.ordinary20_of_triality (h := h) hG hM hu hL e)
      · exact .inr (.triality n (by omega) hm)
  | ree m hm model => exact .inr (.ree m hm model)
  | symplectic_derived hm =>
      obtain ⟨e⟩ := hm
      exact (s.false_of_alternatingSix_equiv (h := h) hG hu hmany hres hL
        (e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix)).elim
  | g2_derived hm =>
      exact .inl (s.ordinary20_of_binaryG2Derived (h := h) hG hM hu hL (Classical.choice hm))
  | tits hm => exact .inl (s.ordinary20_of_tits (h := h) hG hM hu hL (Classical.choice hm))

/-- Exhaust all six marked 1.1.5 alternatives, retaining the two-core quotient of every cover. -/
theorem PreExclusionSource.ordinary20_or_exceptional_of_marked_model
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
    (hp : p = 3 ∨ p = 5)
    {α : MulAut d.L} (hm : ModelAction115 d.L α) :
    d.Ordinary20Alternatives ∨ d.OrdinaryExceptionalHigherField := by
  cases hm with
  | lie _ hm _ =>
      rcases hm with hm | hm | ⟨n,hn,hm⟩
      · exact .inl (s.ordinary20_of_rankOne (h := h) hG hM hu hne hmany hres hL (.inl hm))
      · exact s.ordinary20_or_exceptional_of_rankTwo (h := h) hG hempty hM hJ hu hne hmany hres hL hm
      · exact .inl (s.ordinary20_of_binaryPSL (h := h) hG hM hu hL hn hm)
  | two_cover hc _ hm _ =>
      rcases hm with hm | hm
      · exact .inl (s.ordinary20_of_higherField (h := h) hG hempty hM hJ hu hne hmany hres hL (.inr hm))
      · exact .inr (.g2_cover hc hm)
  | six σ hs ha =>
      exact .inl (s.ordinary20_of_alternating (h := h) hG hu hmany hres hL
        (.inl ⟨σ,hs,ha⟩))
  | seven σ hs ha =>
      exact .inl (s.ordinary20_of_alternating (h := h) hG hu hmany hres hL
        (.inr ⟨σ,hs,ha⟩))
  | odd hm _ =>
      exact .inl (s.ordinary20_of_odd (h := h) hG hM hJ hu hne hmany hres hL hp hm)
  | sporadic name hn hm _ =>
      exact .inl (s.ordinary20_of_sporadic_quotient (h := h) hG hempty hM hJ hu hL name hn hm)

/-- The original hypotheses give an exhaustive reduction at the same component d. -/
theorem PreExclusionSource.ordinary20_or_exceptional
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
    d.Ordinary20Alternatives ∨ d.OrdinaryExceptionalHigherField := by
  obtain ⟨z,hz,hzne⟩ := (bot_or_exists_ne_one (centralInvolutions T)).resolve_left
    (centralInvolutions_ne_bot_of_maximal_local T hM.1)
  obtain ⟨α,_,hm⟩ := s.ordinary_marked_model (h := h) hL hz hzne
  exact s.ordinary20_or_exceptional_of_marked_model (h := h) hG hempty hM hJ hu hne hmany hres hL hp hm

/-- Apply 15.1.21 to every proved initial constructor; only the exceptional models remain. -/
theorem PreExclusionSource.postRankOneModel_or_exceptional
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
    OrdinaryPostRankOneModel (d.L ⧸ pCore 2 d.L) ∨ d.OrdinaryExceptionalHigherField := by
  rcases s.ordinary20_or_exceptional (h := h) hG hempty hM hJ hu hne hmany hres hL hp with ha | he
  · exact .inl (ha.postRankOneModel_of_preExclusion (h := h) s hG hM hJ hu hL hp)
  · exact .inr he

/-- The later exchanged consumer leaves precisely these exceptional models at the same d. -/
theorem ExchangedSource.ordinary_exceptional_of_preExclusion
    (e : d.ExchangedSource)
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
    (hp : p = 3 ∨ p = 5) : d.OrdinaryExceptionalHigherField := by
  rcases s.ordinary20_or_exceptional (h := h) hG hempty hM hJ hu hne hmany hres hL hp with ha | he
  · exact (e.not_ordinary_of_preExclusion_catalogue (h := h) s hG hM hJ hu hp
      (fun _ => ha) hL).elim
  · exact he

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Construct the original component and exhaust its marked models, retaining Z₁, row and prime. -/
theorem PreparedChosenModule.source_preExclusion_ordinary20_or_exceptional
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
        d.Ordinary20Alternatives ∨ d.OrdinaryExceptionalHigherField) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hL => s.ordinary20_or_exceptional (h := h)
    hG hempty hM hJ hu hne hmany hres hL hp⟩

/-- The constructed original component already has the early quotient reduction at that same d. -/
theorem PreparedChosenModule.source_preExclusion_postRankOneModel_or_exceptional
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
        CaseIComponentData.OrdinaryPostRankOneModel (d.L ⧸ pCore 2 d.L) ∨
          d.OrdinaryExceptionalHigherField) := by
  obtain ⟨d,hZ,hr,s,hd⟩ := h.source_preExclusion_ordinary20_or_exceptional
    hG T hempty hM hmany hJ hu hne hfull m hp hres
  refine ⟨d,hZ,hr,s,fun hL => ?_⟩
  rcases hd hL with ha | he
  · exact .inl (ha.postRankOneModel_of_preExclusion (h := h) s hG hM hJ hu hL hp)
  · exact .inr he

end CFSG.Quasithin.Chapter15.Section01
