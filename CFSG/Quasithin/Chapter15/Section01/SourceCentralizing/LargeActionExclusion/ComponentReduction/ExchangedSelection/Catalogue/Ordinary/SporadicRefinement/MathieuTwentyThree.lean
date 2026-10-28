module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.SporadicRefinement.MathieuTwentyFour
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.RankOne.QuinticSylow
public import Theory.Mathieu.M23.Properties.QuinticSylowOvergroups

/-!
# The complete M₂₃ row and all surviving sporadic refinements

The original quintic actor would supply a two-five Sylow overgroup of the
literal M₂₃ quotient. Native heptad and triple geometry excludes it. The
existing cubic calculation supplies the exact residual-centralizer identity
at prime three, completing this Ordinary22 row with central covers intact.
Together with the completed M₂₄ and smaller sporadic rows, this leaves only
the earlier HS and Ru exclusions in the sporadic branch.

The original-marker application preserves d, Z₁, row, prime and the actual
quotient equivalence. HS/Ru and final ordinary assembly remain with
qt-e-15122-ordinary-pre-exclusion. Independent earlier source premises
retain their producers and final discharge with
qt-e-15122-pre-exclusion-catalogue.
Source: Aschbacher–Smith 15.1.21(ii), 15.1.22(5), pp.1098–1100,
refs/quasithin.pdf; GLS3 Table 5.3d for native M₂₃ local geometry.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- The original quintic actor cannot act on an ordinary M₂₃ quotient. -/
theorem PreExclusionSource.not_mathieuTwentyThree_of_prime_five
    (s : d.PreExclusionSource h.normalized 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : (d.L ⧸ pCore 2 d.L) ≃* Sporadic.Mathieu.M23) : False := by
  have hf := s.surviving_sporadic_quotient_facts (h := h)
    (name := .m23) (.inr (.inr (.inl rfl))) e
  obtain ⟨P,H,a,b,hPH,h5,hc⟩ := s.quintic_two_five_sylow_overgroup (h := h) hG hM hJ hL e
    (Theory.SpecificGroups.BinaryComponentResidual.Facts.of_equiv e.symm hf)
  exact Sporadic.Mathieu.M23QuinticSylow.not_five_of_two_five_sylow_overgroup P H hPH a b hc h5

/-- Both original primes give the full Ordinary22 M₂₃ row, with its
literal local residual identity and the original central quotient. -/
theorem PreExclusionSource.ordinary22_of_mathieuTwentyThree_quotient
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : (d.L ⧸ pCore 2 d.L) ≃* Sporadic.Mathieu.M23) : d.Ordinary22Alternatives := by
  rcases hp with hp | rfl
  · exact s.ordinary22_sporadic_of_prime_three (h := h) hp hG hempty hM hu hL
      (name := .m23) (.inr (.inr (.inl rfl))) e
  · exact (s.not_mathieuTwentyThree_of_prime_five (h := h) hG hM hJ hL e).elim

/-- Every surviving sporadic quotient now satisfies every Ordinary22
clause at both source primes. Only the earlier HS/Ru exclusions remain. -/
theorem PreExclusionSource.ordinary22_or_hs_or_ru
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (name : SporadicName) (hn3 : name ≠ .j3) (hn4 : name ≠ .j4)
    (e : (d.L ⧸ pCore 2 d.L) ≃* name.Carrier) :
    d.Ordinary22Alternatives ∨ (name = .hs ∧ p = 3) ∨ name = .ru := by
  rcases s.ordinary22_or_hs_ru_or_mathieuTwentyThree (h := h) hp hG hempty hM hJ hu hL name hn3 hn4 e
      with ha | hs | hr | ⟨_,rfl⟩
  · exact .inl ha
  · exact .inr (.inl hs)
  · exact .inr (.inr hr)
  · exact .inl (s.ordinary22_of_mathieuTwentyThree_quotient (h := h) hp hG hempty hM hJ hu hL e)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
variable {G : Type*} [Group G] [Finite G]

/-- Apply the refined sporadic reduction at the original marker, preserving
the component, Z₁, source row, and either source prime. -/
theorem PreparedChosenModule.source_preExclusion_sporadic_mathieuTwentyThree_refinement
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
        ∀ (name : SporadicName), name ≠ .j3 → name ≠ .j4 →
        ((d.L ⧸ pCore 2 d.L) ≃* name.Carrier) →
        d.Ordinary22Alternatives ∨ (name = .hs ∧ m.prime = 3) ∨ name = .ru) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hL name hn3 hn4 e =>
    s.ordinary22_or_hs_or_ru (h := h) hp hG hempty hM hJ hu hL name hn3 hn4 e⟩

end CFSG.Quasithin.Chapter15.Section01
