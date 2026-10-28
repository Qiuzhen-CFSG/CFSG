module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.SporadicRefinement.Survivors
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Ordinary.Models
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Residual

/-!
# The surviving sporadic Ordinary22 rows at the original prime three

The faithful quotient has two-residual of order three. Its two-residual
and prime-to-three residual therefore move the same subgroup of V. If the
latter lay in M_Z, the original residual-intersection identity would make
it centralize V, contradicting the original moving subgroup's action on L.
Thus cubic escape is proved before exchanged selection.

For each of the six surviving sporadic quotients, its actual center,
three-rank and outer-two facts identify the component as O^{3′}(G₁), and
identify the literal local residuals. The original Sylow-fixer bounds and
centralizer calculation then prove every clause of Ordinary22 row (5).
The M₁₁ theorem completes the sporadic reduction up to HS and Ru at p = 3.
The marker application retains the same d, Z₁, row and source prime.

No parabolic placement or exchanged-plane premise is used. The prime-five
refinements, HS/Ru exclusions, exceptional initial models and remaining Lie
geometry stay with qt-e-15122-ordinary-pre-exclusion. The literal 15.1.14
input remains with qt-e-1514-global-thompson-residual and final discharge
with qt-e-15122-pre-exclusion-catalogue.

Source: Aschbacher--Smith 15.1.18(2), 15.1.22(5)--(6), and the intrinsic
residual argument of 15.1.25(1), printed pp.1092,1099--1102. The latter
argument here uses only its actual rank and model hypotheses.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- At the original prime three, the faithful action already forces escape
of the cubic residual. No exchanged plane or escape premise is used. -/
theorem PreExclusionSource.threeResidual_not_le_MZ
    (s : d.PreExclusionSource h.normalized 3) :
    ¬ (primeToResidual 3 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype ≤ d.MZ := by
  let C := M ⊓ d.G1
  let Y := (primeToResidual 3 C).map C.subtype
  have hY : IsPPerfect 2 Y := (isPPerfect_primeToResidual 3 2 (by decide)).of_surjective
    ((primeToResidual 3 C).equivMapOfInjective C.subtype C.subtype_injective).toMonoidHom
    ((primeToResidual 3 C).equivMapOfInjective C.subtype C.subtype_injective).surjective
  intro hout
  have hc := s.twoPerfect_intersection_centralizes (h := h) hY
    ((map_subtype_le _).trans inf_le_left) hout
  have hv : ⁅V,Y⁆ = ⊥ := by
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hc
  have he := caseI_cubic_commutator_of_residual_card_three h.normalized
    (d.Z1_le_fixed.trans inf_le_left) s.residual_card
  change ⁅V,Y⁆ = ⁅V,(pResidual 2 C).map C.subtype⁆ at he
  apply s.moving_noncentral
  change ⁅d.L,⁅V,(pResidual 2 C).map C.subtype⁆⁆ = ⊥
  rw [← he,hv,commutator_bot_right]

/-- The recognized quotient places the cubic residual in the same component;
its escape is obtained from the original faithful prime-three action. -/
theorem PreExclusionSource.localThreeResidual_escape_of_cubic_model
    (s : d.PreExclusionSource h.normalized 3)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hf : Theory.SpecificGroups.BinaryComponentResidual.Facts (d.L ⧸ pCore 2 d.L)) :
    ¬ d.localThreeResidual ≤ d.ML := by
  let := s.quasisimple
  have he := (d.source_cubic_component hG h hf).2
  intro hh
  apply s.threeResidual_not_le_MZ (h := h)
  rw [he]
  exact hh.trans inf_le_left

/-- The six surviving sporadic models supply the intrinsic residual facts
on the literal two-core quotient, including all retained central covers. -/
theorem PreExclusionSource.surviving_sporadic_quotient_facts
    (_s : d.PreExclusionSource h.normalized p)
    {name : SporadicName}
    (hn : name = .m12 ∨ name = .m22 ∨ name = .m23 ∨ name = .m24 ∨ name = .j2 ∨ name = .he)
    (e : (d.L ⧸ pCore 2 d.L) ≃* name.Carrier) :
    Theory.SpecificGroups.BinaryComponentResidual.Facts (d.L ⧸ pCore 2 d.L) := by
  let : Finite name.Carrier := Finite.of_equiv (d.L ⧸ pCore 2 d.L) e.toEquiv
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
  · exact facts_of_small_model (.inr (.inl ⟨e⟩))
  · exact facts_of_small_model (.inr (.inr (.inl ⟨e⟩)))
  · exact facts_of_small_model (.inr (.inr (.inr (.inl ⟨e⟩))))
  · exact facts_of_small_model (.inr (.inr (.inr (.inr (.inl ⟨e⟩)))))
  · exact facts_of_small_model (.inr (.inr (.inr (.inr (.inr ⟨e⟩)))))
  · exact Theory.SpecificGroups.BinaryComponentResidual.Facts.of_equiv e
      ⟨Held.LocalPairs.center_eq_bot,Held.three_rank_ge_two,Held.outer_isPGroup_two⟩

/-- Every clause of ordinary row (5) at the original prime three. The
residual-escape and model inputs are both discharged before exchanged selection. -/
theorem PreExclusionSource.ordinary22_sporadic_of_prime_three
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {name : SporadicName}
    (hn : name = .m12 ∨ name = .m22 ∨ name = .m23 ∨ name = .m24 ∨ name = .j2 ∨ name = .he)
    (e : (d.L ⧸ pCore 2 d.L) ≃* name.Carrier) : d.Ordinary22Alternatives := by
  subst p
  have hf := s.surviving_sporadic_quotient_facts (h := h) hn e
  have hr := s.localThreeResidual_escape_of_cubic_model (h := h) hG hf
  exact .sporadic name hn
    ⟨(QuotientGroup.quotientMulEquivOfEq (s.ordinary hL).center_eq).trans e⟩
    (s.surviving_sporadic_centralizer_eq (h := h) hG hempty hM hu hL hn e)
    ((s.sporadic_quotient_model_control (h := h) hM.1.2 hu hL hn e).2 hr)

/-- For the initial sporadic family at p = 3, only the earlier HS/Ru
characteristic-subgroup exclusions remain; all other full Ordinary22 rows hold. -/
theorem PreExclusionSource.ordinary22_or_hs_or_ru_of_prime_three
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (name : SporadicName) (hn3 : name ≠ .j3) (hn4 : name ≠ .j4)
    (e : (d.L ⧸ pCore 2 d.L) ≃* name.Carrier) :
    d.Ordinary22Alternatives ∨ name = .hs ∨ name = .ru := by
  have hs (hn : name = .m12 ∨ name = .m22 ∨ name = .m23 ∨
      name = .m24 ∨ name = .j2 ∨ name = .he) : d.Ordinary22Alternatives :=
    s.ordinary22_sporadic_of_prime_three (h := h) hp hG hempty hM hu hL hn e
  cases name with
  | m11 => exact .inl (s.ordinary22_of_mathieuEleven_quotient (h := h) hG hM hu hL e)
  | m12 => exact .inl (hs (.inl rfl))
  | m22 => exact .inl (hs (.inr (.inl rfl)))
  | m23 => exact .inl (hs (.inr (.inr (.inl rfl))))
  | m24 => exact .inl (hs (.inr (.inr (.inr (.inl rfl)))))
  | j2 => exact .inl (hs (.inr (.inr (.inr (.inr (.inl rfl))))))
  | he => exact .inl (hs (.inr (.inr (.inr (.inr (.inr rfl))))))
  | j3 => exact (hn3 rfl).elim
  | j4 => exact (hn4 rfl).elim
  | hs => exact .inr (.inl rfl)
  | ru => exact .inr (.inr rfl)

/-- Under the two original source primes, the only remaining sporadic
refinement branches are prime five and the HS/Ru exclusions. -/
theorem PreExclusionSource.ordinary22_or_quintic_or_hs_or_ru
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (name : SporadicName) (hn3 : name ≠ .j3) (hn4 : name ≠ .j4)
    (e : (d.L ⧸ pCore 2 d.L) ≃* name.Carrier) :
    d.Ordinary22Alternatives ∨ p = 5 ∨ name = .hs ∨ name = .ru := by
  rcases hp with hp | hp
  · rcases s.ordinary22_or_hs_or_ru_of_prime_three (h := h)
      hp hG hempty hM hu hL name hn3 hn4 e with ha | hs | hr
    · exact .inl ha
    · exact .inr (.inr (.inl hs))
    · exact .inr (.inr (.inr hr))
  · exact .inr (.inl hp)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
variable {G : Type*} [Group G] [Finite G]

/-- The original marker supplies the same-d sporadic refinement without
parabolic, exchanged-source, or cubic-escape hypotheses. -/
theorem PreparedChosenModule.source_preExclusion_sporadic_cubic_refinement
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
        d.Ordinary22Alternatives ∨ m.prime = 5 ∨ name = .hs ∨ name = .ru) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hL name hn3 hn4 e =>
    s.ordinary22_or_quintic_or_hs_or_ru (h := h)
      hp hG hempty hM hu hL name hn3 hn4 e⟩

end CFSG.Quasithin.Chapter15.Section01
