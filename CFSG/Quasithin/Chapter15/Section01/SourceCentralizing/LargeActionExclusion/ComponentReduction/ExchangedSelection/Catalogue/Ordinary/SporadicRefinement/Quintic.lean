module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.SporadicRefinement.QuinticAction
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.SporadicRefinement.Cubic
public import Theory.Mathieu.SmallModuleRanks.M12
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.NormalElementaryBound
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.SylowNormalElementary
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismTwoRank
public import Theory.SpecificGroups.Held.SylowNormalSixteen
public import Theory.SpecificGroups.Held.TwoRank.Intrinsic

/-!
# Quintic sporadic exclusions before exchanged selection

The original quintic actor produces an elementary subgroup of the literal
component quotient, normalized by its original full Sylow and of order
at least sixteen. The native M₁₂ rank bound and the normal elementary
bounds for J₂ and HS exclude those three prime-five cases. In Held,
coprime splitting and the rank-six bound force order sixteen; its checked
normalizer is five-free, contradicting the same actual actor.

Combining these exclusions with the prime-three refinement completes every
Ordinary22 clause for M₁₂, J₂ and Held. The sporadic reduction now leaves
HS at prime three, Ru, and M₂₂/M₂₃/M₂₄ at prime five. Its original-marker
application preserves d, Z₁, row, source prime and the two-core quotient,
including all central two-covers. No exchanged-source or additional
parabolic-placement hypothesis enters.

The remaining sporadic and linear geometry obligations stay with
qt-e-15122-ordinary-pre-exclusion. The original 15.1.14 input and full
local-family nonblock theorem retain their existing producers, with final
discharge by qt-e-15122-pre-exclusion-catalogue. This reduction does not
claim completion of those remaining Ordinary22 branches.

Source: Aschbacher--Smith 15.1.19(7), 15.1.21--22 and the intrinsic model
bounds of A.3.15, printed pp.1094,1098--1100 and pp.49--50,
refs/quasithin.pdf. Held's normalizer calculation is in
Theory.SpecificGroups.Held.SylowNormalSixteen.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- M₁₂ has no elementary sixteen, excluding the original quintic actor
even when the actual component is a nontrivial central two-cover. -/
theorem PreExclusionSource.not_mathieuTwelve_of_prime_five
    (s : d.PreExclusionSource h.normalized 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : (d.L ⧸ pCore 2 d.L) ≃* Sporadic.Mathieu.M12) : False := by
  obtain ⟨P,E,hE,_,_,hc⟩ := s.quintic_normal_elementary_quotient (h := h)
    hG hM hJ hL e Sporadic.Mathieu.m12_center_eq_bot
    Sporadic.Mathieu.M12SmallPair.ValueBoundParabolics.outer_isPGroup_two
  have hb := (primeRank_le_iff_elementary_card_le Sporadic.Mathieu.M12).mp
    Sporadic.Mathieu.m12_twoRank_le_three E hE
  norm_num at hb
  omega

/-- The actual J₂ Sylow has no normal elementary subgroup larger than four. -/
theorem PreExclusionSource.not_jankoTwo_of_prime_five
    (s : d.PreExclusionSource h.normalized 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : (d.L ⧸ pCore 2 d.L) ≃* Sporadic.LeechRelated.J2.Carrier) : False := by
  obtain ⟨P,E,hE,hEP,hPE,hc⟩ := s.quintic_normal_elementary_quotient (h := h)
    hG hM hJ hL e Sporadic.LeechRelated.J2.OrdinaryLocal.center_eq_bot
    Sporadic.LeechRelated.J2.outer_isTwoGroup
  let := hE
  have hb := Sporadic.LeechRelated.J2.sylow_normal_elementary_card_le_four P
    (E.subgroupOf P) ((normal_subgroupOf_iff_le_normalizer hEP).mpr hPE)
    (IsElementaryAbelian.subgroupOf hEP)
  rw [Nat.card_congr (subgroupOfEquivOfLe hEP).toEquiv] at hb
  omega

/-- The original quintic HS branch is impossible by the native normal
elementary bound eight. The prime-three characteristic-subgroup exclusion
is a separate source obligation. -/
theorem PreExclusionSource.not_higmanSims_of_prime_five
    (s : d.PreExclusionSource h.normalized 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : (d.L ⧸ pCore 2 d.L) ≃* Sporadic.LeechRelated.HS.Carrier) : False := by
  have ho : IsPGroup 2 (MulAut.Outer Sporadic.LeechRelated.HS.Carrier) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by
      simpa only [pow_one] using Sporadic.LeechRelated.HS.outer_card_dvd_two)
  obtain ⟨P,E,hE,_,hPE,hc⟩ := s.quintic_normal_elementary_quotient (h := h)
    hG hM hJ hL e Sporadic.LeechRelated.HS.BlockNormalizer.center_carrier_eq_bot ho
  have hb := Sporadic.LeechRelated.HS.normal_elementary_card_le_eight P E hE hPE
  omega

/-- A fully moved elementary subgroup in Held has order sixteen. Its
normalizer is five-free because a full Sylow normalizes it. -/
theorem PreExclusionSource.not_held_of_prime_five
    (s : d.PreExclusionSource h.normalized 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : (d.L ⧸ pCore 2 d.L) ≃* Held.He) : False := by
  obtain ⟨P,E,D,hE,hEP,hPE,hD,hED,hEn,_⟩ :=
    s.quintic_normal_elementary_pair_quotient (h := h) hG hM hJ hL e
      Held.LocalPairs.center_eq_bot Held.outer_isPGroup_two
  let := hE
  have hb : Nat.card E ≤ 64 := by
    exact (primeRank_le_iff_elementary_card_le Held.He).mp Held.primeRank_two_le_six E hE
  have hc := card_eq_sixteen_of_quintic_movement E D hD hED hEn hb
  exact Held.sylow_normal_sixteen_normalizer_not_five P E hEP hE hc hPE
    (five_dvd_normalizer_of_quintic_movement E D hD hED hEn)

/-- Both source primes now give the complete M₁₂, J₂ and Held Ordinary22 rows,
with the literal Sylow-center centralizer and local prime-to-three residual. -/
theorem PreExclusionSource.ordinary22_of_small_sporadic_quotient
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {name : SporadicName} (hn : name = .m12 ∨ name = .j2 ∨ name = .he)
    (e : (d.L ⧸ pCore 2 d.L) ≃* name.Carrier) : d.Ordinary22Alternatives := by
  rcases hp with hp | rfl
  · apply s.ordinary22_sporadic_of_prime_three (h := h) hp hG hempty hM hu hL _ e
    rcases hn with rfl | rfl | rfl
    · exact .inl rfl
    · exact .inr (.inr (.inr (.inr (.inl rfl))))
    · exact .inr (.inr (.inr (.inr (.inr rfl))))
  · rcases hn with rfl | rfl | rfl
    · exact (s.not_mathieuTwelve_of_prime_five (h := h) hG hM hJ hL e).elim
    · exact (s.not_jankoTwo_of_prime_five (h := h) hG hM hJ hL e).elim
    · exact (s.not_held_of_prime_five (h := h) hG hM hJ hL e).elim

/-- The initial sporadic family now leaves HS only at prime three, Ru,
and the three remaining quintic Mathieu refinements. All other full rows hold. -/
theorem PreExclusionSource.ordinary22_or_remaining_sporadic
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
      (p = 5 ∧ (name = .m22 ∨ name = .m23 ∨ name = .m24)) := by
  rcases hp with hp | rfl
  · rcases s.ordinary22_or_hs_or_ru_of_prime_three (h := h)
      hp hG hempty hM hu hL name hn3 hn4 e with ha | hs | hr
    · exact .inl ha
    · exact .inr (.inl ⟨hs,hp⟩)
    · exact .inr (.inr (.inl hr))
  · cases name with
    | m11 => exact .inl (s.ordinary22_of_mathieuEleven_quotient (h := h) hG hM hu hL e)
    | m12 => exact (s.not_mathieuTwelve_of_prime_five (h := h) hG hM hJ hL e).elim
    | m22 => exact .inr (.inr (.inr ⟨rfl,.inl rfl⟩))
    | m23 => exact .inr (.inr (.inr ⟨rfl,.inr (.inl rfl)⟩))
    | m24 => exact .inr (.inr (.inr ⟨rfl,.inr (.inr rfl)⟩))
    | j2 => exact (s.not_jankoTwo_of_prime_five (h := h) hG hM hJ hL e).elim
    | he => exact (s.not_held_of_prime_five (h := h) hG hM hJ hL e).elim
    | hs => exact (s.not_higmanSims_of_prime_five (h := h) hG hM hJ hL e).elim
    | ru => exact .inr (.inr (.inl rfl))
    | j3 => exact (hn3 rfl).elim
    | j4 => exact (hn4 rfl).elim

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
variable {G : Type*} [Group G] [Finite G]

/-- Apply the refined sporadic reduction at the original marker, preserving
the component, Z₁, source row, and either source prime. -/
theorem PreparedChosenModule.source_preExclusion_sporadic_quintic_refinement
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
          (m.prime = 5 ∧ (name = .m22 ∨ name = .m23 ∨ name = .m24))) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hL name hn3 hn4 e =>
    s.ordinary22_or_remaining_sporadic (h := h) hp hG hempty hM hJ hu hL name hn3 hn4 e⟩

end CFSG.Quasithin.Chapter15.Section01
