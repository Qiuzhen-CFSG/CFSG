module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Nonsporadic.HigherField.G2
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Nonsporadic.HigherField.Triality
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Nonsporadic.HigherField.Ree

/-!
# Ordinary20 narrowing from the original local nonblock theorem

Every remaining exceptional higher-field model supplies a proper original
parabolic whose solvable residual is an escaping nonblock in L(G₁,S), with
actual PSL₂ quotient. The Ree Suzuki residual has already been placed in
M_Z using the original FF catalogue. The G₂ construction includes the
central G₂(4) covers, and all transports retain the original component d.

The earlier rank-one nonblock containment therefore removes all exceptional
branches of the exhaustive marked-model reduction. Applying 15.1.21 then
supplies the early two-core quotient and the later ordinary-elimination
consumer on the same d. The original-marker application retains Z₁, row,
and either source prime. It assumes no exchanged-plane hypothesis.

RankOneNonblockContainment is the explicit remaining source input from
qt-e-1515-constrained-source-catalogue, on the entire original local family.
It has NOT been discharged here. Final discharge, together with original
15.1.14, remains with qt-e-15122-pre-exclusion-catalogue. The remaining
Ordinary22 refinements stay with qt-e-15122-ordinary-pre-exclusion. Thus
this is a conditional assembly, not an unconditional proof of 15.1.20.
Source: Aschbacher--Smith 15.1.20(2),(3), printed pp.1094--1097, and
15.1.21, printed pp.1097--1098 of refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- The precise earlier 15.1.20(2) nonblock containment still required from
qt-e-1515-constrained-source-catalogue. K ranges over the full local family,
not merely ambient C-components. This is an explicit premise, not a theorem. -/
@[expose] def RankOneNonblockContainment (d : CaseIComponentData T M Mc V) : Prop :=
  ∀ K : Subgroup G, K ∈ Chapter1.LIn d.G1 d.S →
    generalizedFitting K = pCore 2 K →
    (∃ n : ℕ, 1 < n ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2^n)) →
    ¬ ChapterC.IsShort K → K ≤ d.MZ

/-- Every exceptional higher-field row produces the same actual escaping
rank-one nonblock residual. In the Ree row its Suzuki partner is already
absorbed using the proved local FF catalogue. -/
theorem PreExclusionSource.exceptional_escaping_nonblock
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (he : d.OrdinaryExceptionalHigherField) :
    ∃ P K : Subgroup G, P ≤ d.L ∧ d.S ≤ normalizer (P : Set G) ∧
      (solvableResidual P).map P.subtype = K ∧ K ∈ Chapter1.LIn d.G1 d.S ∧
      generalizedFitting K = pCore 2 K ∧ ¬ ChapterC.IsShort K ∧ ¬ K ≤ d.MZ ∧
      ∃ n : ℕ, 1 < n ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2^n) := by
  cases he with
  | g2 n hn hm =>
      obtain ⟨P,K,hP,_,hN,hR,hK,hF,hS,hO,hQ⟩ :=
        s.g2_escaping_nonblock (h := h) hG hL n hn (.inl hm)
      exact ⟨P,K,hP.le,hN,hR,hK,hF,hS,hO,n,hn,hQ⟩
  | triality n hn hm =>
      exact s.triality_escaping_nonblock (h := h) hG hL n hn hm
  | ree m hm model =>
      obtain ⟨P,K,hP,_,hN,hR,hK,hF,hS,hO,hQ⟩ :=
        s.ree_escaping_nonblock (h := h) hG hempty hM hJ hu hL m hm model
      exact ⟨P,K,hP.le,hN,hR,hK,hF,hS,hO,2*m+1,by omega,hQ⟩
  | g2_cover _ hm =>
      obtain ⟨P,K,hP,_,hN,hR,hK,hF,hS,hO,hQ⟩ :=
        s.g2_escaping_nonblock (h := h) hG hL 2 (by decide) (.inr (by simpa using hm))
      exact ⟨P,K,hP.le,hN,hR,hK,hF,hS,hO,2,by decide,hQ⟩

/-- Close exceptional higher-field rows with the exact earlier local-family
nonblock theorem, preserving its full original domain. -/
theorem PreExclusionSource.not_exceptional_of_nonblock_containment
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hlocal : d.RankOneNonblockContainment) : ¬ d.OrdinaryExceptionalHigherField := by
  intro he
  obtain ⟨_,K,_,_,_,hK,hF,hS,hO,hQ⟩ :=
    s.exceptional_escaping_nonblock (h := h) hG hempty hM hJ hu hL he
  exact hO (hlocal K hK hF hQ hS)

/-- The five original Ordinary20 alternatives at the same d, conditional
only on the independently owned earlier nonblock containment (and 15.1.14). -/
theorem PreExclusionSource.ordinary20_of_nonblock_containment
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
    d.Ordinary20Alternatives :=
  (s.ordinary20_or_exceptional (h := h) hG hempty hM hJ hu hne hmany hres hL hp).resolve_right
    (s.not_exceptional_of_nonblock_containment (h := h) hG hempty hM hJ hu hL hlocal)

/-- The actual early two-core quotient follows at that same marking after
15.1.21, with no exchanged-plane or noncentrality hypothesis. -/
theorem PreExclusionSource.postRankOneModel_of_nonblock_containment
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
    OrdinaryPostRankOneModel (d.L ⧸ pCore 2 d.L) := by
  have ha := s.ordinary20_of_nonblock_containment (h := h)
    hG hempty hM hJ hu hne hmany hres hL hp hlocal
  exact ha.postRankOneModel_of_preExclusion (h := h) s hG hM hJ hu hL hp

/-- The later ordinary-elimination consumer uses the same original d and
its earlier local-family containment; the full Ordinary22 refinement is separate. -/
theorem ExchangedSource.not_ordinary_of_nonblock_containment
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
    (hp : p = 3 ∨ p = 5) (hlocal : d.RankOneNonblockContainment) :
    ¬ IsComponent d.G1 (d.L.subgroupOf d.G1) := by
  intro hL
  exact e.not_ordinary_of_preExclusion_catalogue (h := h) s hG hM hJ hu hp
    (fun _ => s.ordinary20_of_nonblock_containment (h := h)
      hG hempty hM hJ hu hne hmany hres hL hp hlocal) hL

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Construct the original d and narrow its ordinary case at that same marking.
The full local-family 15.1.20(2) input remains explicit for the source owner. -/
theorem PreparedChosenModule.source_preExclusion_ordinary_of_nonblock_containment
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
        d.Ordinary20Alternatives ∧
        CaseIComponentData.OrdinaryPostRankOneModel (d.L ⧸ pCore 2 d.L)) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,fun hL hlocal => ?_⟩
  have ha := s.ordinary20_of_nonblock_containment (h := h)
    hG hempty hM hJ hu hne hmany hres hL hp hlocal
  exact ⟨ha,ha.postRankOneModel_of_preExclusion (h := h) s hG hM hJ hu hL hp⟩

end CFSG.Quasithin.Chapter15.Section01
