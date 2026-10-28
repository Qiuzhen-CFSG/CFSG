module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.SporadicRefinement.Cubic
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Nonsporadic.BinaryRankTwo
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.RankOne.PrimeActor
public import Theory.SpecificGroups.G2Even.BinarySylowOvergroups
public import Theory.SpecificGroups.Tits.EscapingSylowOvergroups

/-!
# The original G₂(2)′ and cubic Tits parabolic rows

At the original prime three, the faithful moving subgroup forces the
literal cubic residual to escape M_Z. The intrinsic rank and outer-action
facts identify that residual with O^{3′}(M ∩ L). The actual G₂(2)′ and Tits
Sylow-overgroup geometry then makes M ∩ L the other maximal parabolic.
Both original parabolics, their distinctness and the literal residual
centralizer identity are retained at the same component.

For G₂(2)′ the original prime-five actor is impossible: its actual
automorphism group has order 12096. Thus the G₂(2)′ row is complete at
both source primes. The marker consumer constructs the original component
and applies these results without exchanged-source or parabolic-placement
premises. Tits at prime five, triality, the linear geometry and remaining
sporadic refinements remain with qt-e-15122-ordinary-pre-exclusion; final
catalogue assembly stays with qt-e-15122-pre-exclusion-catalogue.

Source: Aschbacher--Smith 15.1.19(7), 15.1.22(4),(**), printed pp.1094,
1098--1099, and the intrinsic residual argument of 15.1.25(1), p.1102,
refs/quasithin.pdf. The latter argument uses only its proved rank/model
premises here, before any exchanged-component selection.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
open Theory.SpecificGroups.BinaryComponentResidual
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

private theorem ordinary22_of_cubic_sylow_overgroups
    (s : d.PreExclusionSource h.normalized 3)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hm : OrdinaryBinaryRankTwo d.L)
    (hmarked : d.ML = d.L ⊓ centralizer ((center d.SL).map d.SL.subtype : Set G))
    (hf : Facts (d.L ⧸ pCore 2 d.L))
    (hself : ∀ P : Sylow 2 d.L, normalizer (P : Set d.L) = P)
    (hmax : ∀ P : Sylow 2 d.L,
      IsCoatom (centralizer ((center P).map (P : Subgroup d.L).subtype : Set d.L)))
    (hother : ∀ (P : Sylow 2 d.L) (H : Subgroup d.L), H ≠ ⊤ → (P : Subgroup d.L) ≤ H →
      ¬ H ≤ centralizer ((center P).map (P : Subgroup d.L).subtype : Set d.L) → IsCoatom H) :
    d.Ordinary22Alternatives := by
  obtain ⟨P,hP⟩ := s.component_sylow
  have hloc := s.local_intersections (h := h) hG hu hTM
  have hr := s.localThreeResidual_escape_of_cubic_model (h := h) hG hf
  have hSL : d.SL.subgroupOf d.L = (P : Subgroup d.L) := by
    apply map_injective (f := d.L.subtype) d.L.subtype_injective
    rw [map_subgroupOf_eq_of_le (show d.SL ≤ d.L from inf_le_right),hP]
  have hB : d.ordinaryBorel = d.SL := by
    change (normalizer (d.SL.subgroupOf d.L : Set d.L)).map d.L.subtype = _
    rw [hSL]
    change (normalizer (P : Set d.L)).map d.L.subtype = d.SL
    rw [hself P,hP]
  have hZ : ((center P).map (P : Subgroup d.L).subtype).map d.L.subtype =
      (center d.SL).map d.SL.subtype := by
    rw [map_map, ← map_center_image_of_injective (P : Subgroup d.L)
      d.L.subtype d.L.subtype_injective, hP]
  have hC : d.ML.subgroupOf d.L =
      centralizer ((center P).map (P : Subgroup d.L).subtype : Set d.L) := by
    rw [hmarked]
    ext x
    constructor
    · intro hx z hz
      exact Subtype.ext (hx.2 z (hZ ▸ mem_map_of_mem d.L.subtype hz))
    · intro hx
      refine ⟨x.property, ?_⟩
      intro z hz
      obtain ⟨w,hw,rfl⟩ := hZ.symm ▸ hz
      exact congrArg Subtype.val (hx w hw)
  have hout : ¬ M ⊓ d.L ≤ d.ML := fun hh => hr ((map_subtype_le _).trans hh)
  have hother' : IsCoatom ((M ⊓ d.L).subgroupOf d.L) := by
    apply hother P _
    · intro he
      exact (not_le_of_gt hloc.2.2.2.2.1) (subgroupOf_eq_top.mp he)
    · rw [← hSL]
      exact comap_mono hloc.2.2.2.1
    · rw [← hC]
      intro hh
      have he := map_mono (f := d.L.subtype) hh
      rw [map_subgroupOf_eq_of_le inf_le_right,
        map_subgroupOf_eq_of_le (show d.ML ≤ d.L from inf_le_right)] at he
      exact hout he
  exact .binaryRankTwo hm hmarked ⟨hloc.2.2.1,hB ▸ hloc.2.1⟩
    ⟨hloc.2.2.2.2.1,hB ▸ hloc.2.2.2.1⟩ (hC.symm ▸ hmax P) hother'
    (fun he => hout he.ge) ((s.binaryRankTwo_model_control (h := h) hTM hu hL hm).2 hr)

private noncomputable def quotientOfCenterlessModel
    (s : d.PreExclusionSource h.normalized 3)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {X : Type*} [Group X] (e : d.L ≃* X) (hx : center X = ⊥) :
    (d.L ⧸ pCore 2 d.L) ≃* X := by
  have hcen : center d.L = ⊥ := by
    apply bot_unique
    intro x hxc
    have he := (centerCongr e ⟨x,hxc⟩).property
    change e x ∈ center X at he
    rw [hx,mem_bot] at he
    exact mem_bot.mpr (e.injective (he.trans (map_one e).symm))
  exact ((QuotientGroup.quotientMulEquivOfEq
    ((s.ordinary hL).center_eq.symm.trans hcen)).trans QuotientGroup.quotientBot).trans e

/-- Every clause of ordinary row (4) for G₂(2)′ at the original prime
three, with the original M ∩ L as its other maximal parabolic. -/
theorem PreExclusionSource.ordinary22_binaryG2Derived_of_prime_three
    (s : d.PreExclusionSource h.normalized 3)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : d.L ≃* commutator (Atlas.G2.Model (ZMod 2))) : d.Ordinary22Alternatives := by
  have hc := s.centralizer_eq_of_sylow_fixers (h := h) hG hM hu hL e
    (fun P a _ ha => by
      obtain ⟨t,_,ht⟩ := Atlas.G2.EvenInvolutionGeometry.binary_fixing_sylow_inner
        Atlas.G2.LieAutomorphismExtensions.binaryConjugation_bijective P a ha
      exact ⟨t,ht⟩)
    (Atlas.G2.BinarySylowCenterMaximal.centralizer_isCoatom e)
  have hf := Facts.of_equiv (quotientOfCenterlessModel (h := h) s hL e g2.1) g2
  exact ordinary22_of_cubic_sylow_overgroups (h := h) s hG hM.1.2 hu hL (.inl ⟨e⟩) hc hf
    (fun P => (Atlas.G2.BinarySylowOvergroups.sylow_geometry e P).1)
    (fun P => (Atlas.G2.BinarySylowOvergroups.sylow_geometry e P).2.1)
    (fun P => (Atlas.G2.BinarySylowOvergroups.sylow_geometry e P).2.2)

/-- Every clause of ordinary row (4) for the Tits group at the original
prime three. Sylow-overgroup coverage identifies the second parabolic. -/
theorem PreExclusionSource.ordinary22_tits_of_prime_three
    (s : d.PreExclusionSource h.normalized 3)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : d.L ≃* Tits.ParrottGroup) : d.Ordinary22Alternatives := by
  have hc := s.centralizer_eq_of_sylow_fixers (h := h) hG hM hu hL e
    (fun P a _ ha => by
      obtain ⟨t,_,ht⟩ := Tits.SylowPointwiseInner.parrott_fixing_sylow_inner P a ha
      exact ⟨t,ht⟩)
    (Tits.SylowCenterMaximal.centralizer_isCoatom e)
  have hf := Facts.of_equiv (quotientOfCenterlessModel (h := h) s hL
    (e.trans Tits.parrottFiniteImageEquiv) tits_facts.1) tits_facts
  exact ordinary22_of_cubic_sylow_overgroups (h := h) s hG hM.1.2 hu hL (.inr (.inl ⟨e⟩)) hc hf
    (fun P => (Tits.BinarySylowOvergroups.sylow_geometry e P).1)
    (fun P => (Tits.BinarySylowOvergroups.sylow_geometry e P).2.1)
    (fun P => (Tits.BinarySylowOvergroups.sylow_geometry e P).2.2)

/-- At prime three, the only remaining binary rank-two geometry is the
genuine triality row. The G₂(2)′ and Tits parabolic rows are fully discharged. -/
theorem PreExclusionSource.ordinary22_or_triality_of_binaryRankTwo_prime_three
    (s : d.PreExclusionSource h.normalized 3)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hm : OrdinaryBinaryRankTwo d.L) :
    d.Ordinary22Alternatives ∨ Nonempty (d.L ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) := by
  rcases hm with he | he | he
  · exact .inl (s.ordinary22_binaryG2Derived_of_prime_three (h := h) hG hM hu hL (Classical.choice he))
  · exact .inl (s.ordinary22_tits_of_prime_three (h := h) hG hM hu hL (Classical.choice he))
  · exact .inr he

/-- The original prime-five actor cannot act nontrivially on G₂(2)′,
since its actual automorphism group has order 12096. -/
theorem PreExclusionSource.not_binaryG2Derived_of_prime_five
    (s : d.PreExclusionSource h.normalized 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (e : d.L ≃* commutator (Atlas.G2.Model (ZMod 2))) : False := by
  obtain ⟨Y,hY,hn,hout⟩ := s.rankOne_prime_actor_noncentral (h := h) hG hM hJ
  let a := (MulAut.congr e).toMonoidHom.comp
    (d.L.normalizerMonoidHom.comp (inclusion hn))
  have ha (y : Y) : a y = 1 := by
    obtain ⟨k,hk⟩ := hY.prime_group y
    have hp : (a y) ^ (5 ^ k) = 1 := by rw [← map_pow,hk,map_one]
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes
      ((by decide : Nat.Coprime 5 12096).pow_left k) (orderOf_dvd_of_pow_eq_one hp)
    have hc : Nat.card (MulAut (commutator (Atlas.G2.Model (ZMod 2)))) = 12096 :=
      (Nat.card_congr Atlas.G2.LieAutomorphismExtensions.binaryAutomorphismEquiv.toEquiv).symm.trans
        Atlas.G2.LieAutomorphismExtensions.card_binaryFull
    simpa only [hc] using orderOf_dvd_natCard (a y)
  apply hout
  intro y hy
  have he : d.L.normalizerMonoidHom (inclusion hn ⟨y,hy⟩) = 1 := by
    apply (MulAut.congr e).injective
    exact (ha ⟨y,hy⟩).trans (map_one (MulAut.congr e)).symm
  have hk : inclusion hn ⟨y,hy⟩ ∈ d.L.normalizerMonoidHom.ker := he
  rw [normalizerMonoidHom_ker] at hk
  exact hk

/-- The G₂(2)′ row is complete for both original source primes. The
prime-five case is excluded by the genuine original prime actor. -/
theorem PreExclusionSource.ordinary22_of_binaryG2Derived
    {p : ℕ} (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : d.L ≃* commutator (Atlas.G2.Model (ZMod 2))) : d.Ordinary22Alternatives := by
  rcases hp with rfl | rfl
  · exact s.ordinary22_binaryG2Derived_of_prime_three (h := h) hG hM hu hL e
  · exact (s.not_binaryG2Derived_of_prime_five (h := h) hG hM hJ e).elim

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Apply the complete G₂(2)′ row and the cubic rank-two refinement to
the original marker, preserving its component, Z₁, row and source prime. -/
theorem PreparedChosenModule.source_preExclusion_binary_rankTwo_refinement
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
        (Nonempty (d.L ≃* commutator (Atlas.G2.Model (ZMod 2))) → d.Ordinary22Alternatives) ∧
        (m.prime = 3 → CaseIComponentData.OrdinaryBinaryRankTwo d.L →
          d.Ordinary22Alternatives ∨
            Nonempty (d.L ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one))) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,fun hL => ⟨?_,?_⟩⟩
  · rintro ⟨e⟩
    exact s.ordinary22_of_binaryG2Derived (h := h) hp hG hM hJ hu hL e
  · intro hp3 hm
    have s3 : d.PreExclusionSource h.normalized 3 := hp3 ▸ s
    exact s3.ordinary22_or_triality_of_binaryRankTwo_prime_three (h := h) hG hM hu hL hm

end CFSG.Quasithin.Chapter15.Section01
