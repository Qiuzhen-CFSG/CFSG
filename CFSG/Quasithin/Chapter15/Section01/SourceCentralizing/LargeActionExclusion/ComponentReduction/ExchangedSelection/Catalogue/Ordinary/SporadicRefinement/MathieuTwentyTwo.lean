module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.SporadicRefinement.Quintic
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.RankOne.QuinticSylow
public import Theory.Mathieu.M22.Properties.QuinticSylowOvergroups

/-!
# The complete M₂₂ row before exchanged selection

The original permuting quintic actor would give a subgroup of the literal
M₂₂ quotient containing a full Sylow two-subgroup, with order divisible by
five and prime to three and eleven. The native pair/hexad calculation
forces that subgroup to have order 128, a contradiction. Prime three is
already handled by the genuine local cubic-residual escape. Together these
prove every Ordinary22 clause for M₂₂, including central two-covers.

The refined sporadic reduction and its original-marker application retain
the same component, Z₁, source row, prime and quotient marking. Only M₂₃
and M₂₄ remain among quintic Mathieu rows; HS at prime three and Ru still
require their earlier source exclusions. Those and final ordinary assembly
stay with qt-e-15122-ordinary-pre-exclusion. The independent earlier source
premises retain their producers and final discharge with
qt-e-15122-pre-exclusion-catalogue.
Source: Aschbacher--Smith 15.1.21(ii), 15.1.22(5), printed pp.1098--1100,
refs/quasithin.pdf; native M₂₂ geometry E.4.3(2), pp.241--242.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- The original quintic actor cannot act on an ordinary M₂₂ quotient. -/
theorem PreExclusionSource.not_mathieuTwentyTwo_of_prime_five
    (s : d.PreExclusionSource h.normalized 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : (d.L ⧸ pCore 2 d.L) ≃* Sporadic.Mathieu.M22) : False := by
  have hf := s.surviving_sporadic_quotient_facts (h := h)
    (name := .m22) (.inr (.inl rfl)) e
  obtain ⟨P,H,a,b,hPH,h5,hc⟩ := s.quintic_two_five_sylow_overgroup (h := h) hG hM hJ hL e
    (Theory.SpecificGroups.BinaryComponentResidual.Facts.of_equiv e.symm hf)
  have h3 : ¬3 ∣ Nat.card H := Nat.prime_three.coprime_iff_not_dvd.mp
    ((((by decide : Nat.Coprime 3 2).pow_right a).mul_right
      ((by decide : Nat.Coprime 3 5).pow_right b)).of_dvd_right hc)
  have h11 : ¬11 ∣ Nat.card H := (by decide : Nat.Prime 11).coprime_iff_not_dvd.mp
    ((((by decide : Nat.Coprime 11 2).pow_right a).mul_right
      ((by decide : Nat.Coprime 11 5).pow_right b)).of_dvd_right hc)
  rw [Sporadic.Mathieu.M22QuinticSylow.card_eq_128 P H hPH h3 h11] at h5
  norm_num at h5

/-- Both original primes give the full Ordinary22 M₂₂ row, with its
literal local residual identity and the original central quotient. -/
theorem PreExclusionSource.ordinary22_of_mathieuTwentyTwo_quotient
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : (d.L ⧸ pCore 2 d.L) ≃* Sporadic.Mathieu.M22) : d.Ordinary22Alternatives := by
  rcases hp with hp | rfl
  · exact s.ordinary22_sporadic_of_prime_three (h := h) hp hG hempty hM hu hL
      (name := .m22) (.inr (.inl rfl)) e
  · exact (s.not_mathieuTwentyTwo_of_prime_five (h := h) hG hM hJ hL e).elim

/-- The remaining quintic Mathieu branches are now exactly M₂₃ and M₂₄.
The earlier HS/Ru exclusions remain independent obligations. -/
theorem PreExclusionSource.ordinary22_or_hs_ru_or_large_mathieu
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (name : SporadicName) (hn3 : name ≠ .j3) (hn4 : name ≠ .j4)
    (e : (d.L ⧸ pCore 2 d.L) ≃* name.Carrier) :
    d.Ordinary22Alternatives ∨ (name = .hs ∧ p = 3) ∨ name = .ru ∨
      (p = 5 ∧ (name = .m23 ∨ name = .m24)) := by
  rcases s.ordinary22_or_remaining_sporadic (h := h) hp hG hempty hM hJ hu hL name hn3 hn4 e
      with ha | hs | hr | ⟨hp5,hm⟩
  · exact .inl ha
  · exact .inr (.inl hs)
  · exact .inr (.inr (.inl hr))
  · rcases hm with rfl | hm
    · exact .inl (s.ordinary22_of_mathieuTwentyTwo_quotient (h := h) hp hG hempty hM hJ hu hL e)
    · exact .inr (.inr (.inr ⟨hp5,hm⟩))

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
variable {G : Type*} [Group G] [Finite G]

/-- Apply the refined sporadic reduction at the original marker, preserving
the component, Z₁, source row, and either source prime. -/
theorem PreparedChosenModule.source_preExclusion_sporadic_mathieu_refinement
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
        d.Ordinary22Alternatives ∨ (name = .hs ∧ m.prime = 3) ∨ name = .ru ∨
          (m.prime = 5 ∧ (name = .m23 ∨ name = .m24))) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hL name hn3 hn4 e =>
    s.ordinary22_or_hs_ru_or_large_mathieu (h := h) hp hG hempty hM hJ hu hL name hn3 hn4 e⟩

end CFSG.Quasithin.Chapter15.Section01
