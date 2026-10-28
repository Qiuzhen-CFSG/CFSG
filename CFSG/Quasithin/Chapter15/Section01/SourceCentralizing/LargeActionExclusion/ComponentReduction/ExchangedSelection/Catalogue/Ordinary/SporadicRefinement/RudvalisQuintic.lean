module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.SporadicRefinement.MathieuTwentyThree
public import Theory.SpecificGroups.Rudvalis.Model.SylowElementarySixteen
public import Theory.SpecificGroups.Rudvalis.Model.TwoRankSix

/-!
# The quintic Rudvalis exclusion and surviving sporadic rows

The original quintic actor gives a Sylow-normal elementary subgroup of the
literal ordinary quotient, moved by a group of order five. The Rudvalis
six-rank bound forces its order to be sixteen. Its intrinsic normalizer
has order prime to five, contradicting that movement. The simplicity used
in the outer-automorphism bound comes from the actual ordinary central quotient.

Together with the completed Mathieu, Janko-two and Held refinements this
proves every surviving sporadic row, at both source primes and with central
covers intact. Only the prime-three HS and Ru characteristic-subgroup
exclusions remain with qt-e-15122-ordinary-pre-exclusion. The original-marker
application preserves d, Z₁, row, prime and the literal quotient equivalence.
Independent earlier source premises retain their producers and final discharge
with qt-e-15122-pre-exclusion-catalogue.

Source: Aschbacher--Smith 15.1.21(ii), 15.1.22(5),(6), printed pp.1098--1100,
refs/quasithin.pdf; GLS3 Table 5.3r for the intrinsic Rudvalis normalizers.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- The original prime-five Rudvalis branch contradicts its intrinsic
normalizer bound for Sylow-normal elementary sixteen-groups. -/
theorem PreExclusionSource.not_rudvalis_of_prime_five
    (s : d.PreExclusionSource h.normalized 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : (d.L ⧸ pCore 2 d.L) ≃* Rudvalis.Model) : False := by
  let : IsQuasisimple d.L := IsQuasisimple.of_mulEquiv (hG := hL.2)
    (subgroupOfEquivOfLe d.L_component.1)
  let : IsSimpleGroup (d.L ⧸ center d.L) := IsQuasisimple.simple
  let f := (QuotientGroup.quotientMulEquivOfEq (s.ordinary hL).center_eq).trans e
  let : IsSimpleGroup Rudvalis.Model := f.symm.isSimpleGroup
  obtain ⟨P,E,D,hE,_,hPE,hD,hED,hEn,_⟩ := s.quintic_normal_elementary_pair_quotient
    (h := h) hG hM hJ hL e Rudvalis.LowCentralizers.model_center_eq_bot Rudvalis.outer_isPGroup_two
  let := hE
  have hb : Nat.card E ≤ 64 :=
    (primeRank_le_iff_elementary_card_le Rudvalis.Model).mp Rudvalis.primeRank_le_six E hE
  have hc := card_eq_sixteen_of_quintic_movement E D hD hED hEn hb
  exact Rudvalis.SylowElementarySixteen.normalizer_sixteen_not_five P E hE hc hPE
    (five_dvd_normalizer_of_quintic_movement E D hD hED hEn)

/-- The full surviving sporadic family satisfies the literal Ordinary22
conclusion at both primes. The two excluded sporadic models remain only
at prime three, pending their earlier characteristic-subgroup arguments. -/
theorem PreExclusionSource.ordinary22_or_cubic_hs_ru
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (name : SporadicName) (hn3 : name ≠ .j3) (hn4 : name ≠ .j4)
    (e : (d.L ⧸ pCore 2 d.L) ≃* name.Carrier) :
    d.Ordinary22Alternatives ∨ (p = 3 ∧ (name = .hs ∨ name = .ru)) := by
  rcases s.ordinary22_or_hs_or_ru (h := h) hp hG hempty hM hJ hu hL name hn3 hn4 e
      with ha | ⟨hn,hp⟩ | rfl
  · exact .inl ha
  · exact .inr ⟨hp,.inl hn⟩
  · rcases hp with hp | rfl
    · exact .inr ⟨hp,.inr rfl⟩
    · exact (s.not_rudvalis_of_prime_five (h := h) hG hM hJ hL e).elim

/-- Every sporadic quotient retained by source 15.1.22 has the full row
under the original pre-selection hypotheses, with no local callback. -/
theorem PreExclusionSource.ordinary22_of_surviving_sporadic_quotient
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (name : SporadicName) (hn : name = .m11 ∨ name = .m12 ∨ name = .m22 ∨
      name = .m23 ∨ name = .m24 ∨ name = .j2 ∨ name = .he)
    (e : (d.L ⧸ pCore 2 d.L) ≃* name.Carrier) : d.Ordinary22Alternatives := by
  have h3 : name ≠ .j3 := by rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> intro he <;> cases he
  have h4 : name ≠ .j4 := by rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> intro he <;> cases he
  rcases s.ordinary22_or_cubic_hs_ru (h := h) hp hG hempty hM hJ hu hL name h3 h4 e
      with ha | ⟨_,he⟩
  · exact ha
  · rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases he <;> contradiction

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
variable {G : Type*} [Group G] [Finite G]

/-- Apply the refined sporadic reduction at the original marker, preserving
the component, Z₁, source row, and either source prime. -/
theorem PreparedChosenModule.source_preExclusion_sporadic_final_refinement
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
        d.Ordinary22Alternatives ∨ (m.prime = 3 ∧ (name = .hs ∨ name = .ru))) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hL name hn3 hn4 e =>
    s.ordinary22_or_cubic_hs_ru (h := h) hp hG hempty hM hJ hu hL name hn3 hn4 e⟩

end CFSG.Quasithin.Chapter15.Section01
