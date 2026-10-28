module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.LieParabolics.CubicRankTwo
public import Theory.SpecificGroups.Tits.FiveSylowOvergroups
public import Theory.GroupAction.ComponentRankAction.OuterTwo
public import Theory.SpecificGroups.Triality.BinaryPrimeActors
public import CFSG.Quasithin.Chapter15.Section01.CaseI.SourceTrialityExclusion

/-!
# Tits completion and the original binary rank-two prime reduction

The Tits carrier has five-rank two and two-group outer automorphisms.
The original ambient rank bound therefore identifies L with O^{5′}(G₁).
The constructed quintic actor belongs to L and to M ∩ L. The actual Tits
Sylow-overgroup coverage places every such five-subgroup in C_L(Z(S_L))
= M_L. Original 15.1.18(2) then makes it centralize V, contradicting its
prescribed movement. Together with the checked cubic parabolic construction,
this completes every clause of the Tits Ordinary22 row at both source primes.

The five-free automorphism group of genuine binary triality also excludes
prime five. At prime three its genuine cubic-action residual theorem gives
escape of the literal O^{3′}(M ∩ L); the already proved Sylow-fixer bound
then supplies the exact residual-centralizer identity. No two-group claim
is made about the triality outer automorphism group.

The final application retains the same d, Z₁, row and prime from the original
marker. The `BinaryRankTwo` extension completes the triality parabolic identification.
Linear geometry and the remaining sporadic refinements stay with
qt-e-15122-ordinary-pre-exclusion. The literal
15.1.14 input and final source catalogue discharge stay with
qt-e-15122-pre-exclusion-catalogue. This extension uses neither exchanged
selection nor an additional parabolic-placement premise.

Source: Aschbacher--Smith, original 15.1.18(2), 15.1.22(4),(**), 15.1.23,
printed pp.1092,1098--1100, and A.3.18, pp.51--53, refs/quasithin.pdf.
The alternative quintic argument uses only those original rank and action
hypotheses, with the actual Tits five-local and Sylow-overgroup certificates.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- Full odd-prime rank and a two-group outer action identify the original
ordinary component with the literal prime-to-p residual of G₁. -/
theorem PreExclusionSource.prime_residual_of_centerless_model
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (ho : Odd p) {X : Type*} [Group X]
    (e : d.L ≃* X) (hz : center X = ⊥)
    (hr : 2 ≤ primeRank p X) (hout : IsPGroup 2 (MulAut.Outer X)) :
    d.L = (primeToResidual p d.G1).map d.G1.subtype := by
  let := h.elementary
  let : Fact p.Prime := ⟨s.prime_prime⟩
  have hZp : IsPGroup 2 d.Z1 :=
    (IsElementaryAbelian.isPGroup 2 V).to_le (d.Z1_le_fixed.trans inf_le_left)
  have hrG : primeRank p d.G1 ≤ 2 :=
    (caseI_centralizer_sqtk hG d.Z1 d.Z1_ne_bot hZp).stronglyQuasithin p s.prime_prime ho
  let K := d.L.subgroupOf d.G1
  let a : K ≃* X := (subgroupOfEquivOfLe d.L_component.1).trans e
  have hc : center K = ⊥ := by
    apply bot_unique
    intro x hx
    have he := (centerCongr a ⟨x,hx⟩).property
    change a x ∈ center X at he
    rw [hz,mem_bot] at he
    exact mem_bot.mpr (a.map_eq_one_iff.mp he)
  let q : (K ⧸ center K) ≃* X :=
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).trans a
  let : Finite X := Finite.of_equiv d.L e.toEquiv
  have hrK : 2 ≤ primeRank p K := by rw [primeRank_equiv p a]; exact hr
  have he := (Theory.GroupAction.ComponentRankAction.component_eq_primeClosure_and_residual_of_outer_twoGroup
    hL (by rw [hc]; simp) hrK hrG q ho hout).2
  have hm := congrArg (map d.G1.subtype) he
  rwa [map_subgroupOf_eq_of_le (show d.L ≤ d.G1 from d.L_component.1)] at hm

/-- The Tits model has full five-rank, so its original component is O^{5′}(G₁). -/
theorem PreExclusionSource.tits_five_residual
    (s : d.PreExclusionSource h.normalized 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : d.L ≃* Tits.ParrottGroup) :
    d.L = (primeToResidual 5 d.G1).map d.G1.subtype := by
  apply s.prime_residual_of_centerless_model (h := h) hG hL (by decide) e
  · exact Tits.RelativeSylowMarking.center_eq_bot Tits.parrottFiniteImageEquiv
  · exact Tits.FiveSylowOvergroups.five_rank_ge_two
  · exact Tits.OuterOddSubgroups.parrott_outer_isPGroup

/-- The original quintic actor lies in L and in a proper Sylow overgroup.
The Tits parabolic orders force it into M_L, contradicting its movement. -/
theorem PreExclusionSource.not_tits_of_prime_five
    (s : d.PreExclusionSource h.normalized 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : d.L ≃* Tits.ParrottGroup) : False := by
  have hres := s.tits_five_residual (h := h) hG hL e
  obtain ⟨Y,hY,hYR⟩ := s.rankOne_prime_actor (h := h) hG hM hJ
  have hYMG : Y ≤ M ⊓ d.G1 := hYR.trans (map_subtype_le _)
  have hYL : Y ≤ d.L := by
    rw [hres]
    intro y hy
    obtain ⟨k,hk⟩ := hY.prime_group ⟨y,hy⟩
    exact ⟨⟨y,(hYMG hy).2⟩,mem_primeToResidual_of_pow (p := 5) (n := k)
      (Subtype.ext (congrArg (fun x : Y => (x : G)) hk)),rfl⟩
  have hmarked := s.centralizer_eq_of_sylow_fixers (h := h) hG hM hu hL e
    (fun P a _ ha => by
      obtain ⟨t,_,ht⟩ := Tits.SylowPointwiseInner.parrott_fixing_sylow_inner P a ha
      exact ⟨t,ht⟩)
    (Tits.SylowCenterMaximal.centralizer_isCoatom e)
  obtain ⟨P,hP⟩ := s.component_sylow
  have hloc := s.local_intersections (h := h) hG hu hM.1.2
  have hSL : d.SL.subgroupOf d.L = (P : Subgroup d.L) := by
    apply map_injective (f := d.L.subtype) d.L.subtype_injective
    rw [map_subgroupOf_eq_of_le (show d.SL ≤ d.L from inf_le_right),hP]
  have hZ : ((center P).map (P : Subgroup d.L).subtype).map d.L.subtype =
      (center d.SL).map d.SL.subtype := by
    rw [map_map, ← map_center_image_of_injective (P : Subgroup d.L)
      d.L.subtype d.L.subtype_injective, hP]
  have hfive : Y.subgroupOf d.L ≤ centralizer
      ((center P).map (P : Subgroup d.L).subtype : Set d.L) := by
    apply Tits.FiveSylowOvergroups.five_subgroup_le_sylow_center_centralizer e P
      ((M ⊓ d.L).subgroupOf d.L) (Y.subgroupOf d.L)
    · intro he
      exact (not_le_of_gt hloc.2.2.2.2.1) (subgroupOf_eq_top.mp he)
    · rw [← hSL]
      exact comap_mono hloc.2.2.2.1
    · exact comap_mono (le_inf (hYMG.trans inf_le_left) hYL)
    · exact hY.prime_group.of_injective (subgroupOfEquivOfLe hYL).toMonoidHom
        (subgroupOfEquivOfLe hYL).injective
  have hYML : Y ≤ d.ML := by
    rw [hmarked]
    refine le_inf hYL ?_
    intro y hy z hz
    obtain ⟨w,hw,rfl⟩ := hZ.symm ▸ hz
    exact congrArg Subtype.val (hfive (show (⟨y,hYL hy⟩ : d.L) ∈ Y.subgroupOf d.L from hy) w hw)
  have hpY : IsPPerfect 2 Y := by
    intro N hN hQ
    let := hN
    have h5 := hY.prime_group.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
    obtain ⟨a,ha⟩ := h5.exists_card_eq
    obtain ⟨b,hb⟩ := hQ.exists_card_eq
    apply index_eq_one.mp
    change Nat.card (Y ⧸ N) = 1
    apply Nat.eq_one_of_dvd_coprimes ((by decide : Nat.Coprime 5 2).pow a b)
    · rw [ha]
    · rw [hb]
  have hcentral := s.twoPerfect_intersection_centralizes (h := h) hpY
    (hYMG.trans inf_le_left) (hYML.trans inf_le_left)
  let W := ⁅V,(pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype⁆
  have hWV : W ≤ V := le_normalizer_iff_commutator_le_left.mp
    (((map_subtype_le _).trans inf_le_left).trans h.normalized)
  have hmove : ⁅W,Y⁆ = ⊥ := by
    rw [commutator_comm]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact hcentral.trans (centralizer_le hWV)
  have hmoving : W = ⊥ := hY.moves.symm.trans hmove
  apply s.moving_noncentral
  change ⁅d.L,W⁆ = ⊥
  rw [hmoving,commutator_bot_right]

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Every clause of the original Tits row at either source prime.
The prime-five case is excluded before any exchanged-component selection. -/
theorem PreExclusionSource.ordinary22_of_tits
    {p : ℕ} (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : d.L ≃* Tits.ParrottGroup) : d.Ordinary22Alternatives := by
  rcases hp with rfl | rfl
  · exact s.ordinary22_tits_of_prime_three (h := h) hG hM hu hL e
  · exact (s.not_tits_of_prime_five (h := h) hG hM hJ hu hL e).elim

/-- Binary triality has five-free full automorphism group, so the original
noncentral quintic actor is impossible on that genuine carrier. -/
theorem PreExclusionSource.not_binaryTriality_of_prime_five
    (s : d.PreExclusionSource h.normalized 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (e : d.L ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) : False := by
  obtain ⟨Y,hY,hn,hout⟩ := s.rankOne_prime_actor_noncentral (h := h) hG hM hJ
  let a := (MulAut.congr e).toMonoidHom.comp
    (d.L.normalizerMonoidHom.comp (inclusion hn))
  have hc : Nat.Coprime 5 (Nat.card (MulAut (Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one))) :=
    (by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr
      Triality.Standard.BinaryPrimeActors.five_not_dvd_card_aut
  have ha (y : Y) : a y = 1 := by
    obtain ⟨k,hk⟩ := hY.prime_group y
    have hp : (a y) ^ (5 ^ k) = 1 := by rw [← map_pow,hk,map_one]
    apply orderOf_eq_one_iff.mp
    exact Nat.eq_one_of_dvd_coprimes (hc.pow_left k)
      (orderOf_dvd_of_pow_eq_one hp) (orderOf_dvd_natCard (a y))
  apply hout
  intro y hy
  have he : d.L.normalizerMonoidHom (inclusion hn ⟨y,hy⟩) = 1 := by
    apply (MulAut.congr e).injective
    exact (ha ⟨y,hy⟩).trans (map_one (MulAut.congr e)).symm
  have hk : inclusion hn ⟨y,hy⟩ ∈ d.L.normalizerMonoidHom.ker := he
  rw [normalizerMonoidHom_ker] at hk
  exact hk

/-- Every surviving binary rank-two row is cubic under the original hypotheses. -/
theorem PreExclusionSource.prime_three_of_binaryRankTwo
    {p : ℕ} (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hm : OrdinaryBinaryRankTwo d.L) : p = 3 := by
  rcases hp with hp | rfl
  · exact hp
  unfold OrdinaryBinaryRankTwo at hm
  rcases hm with he | he | he <;> obtain ⟨e⟩ := he
  · exact (s.not_binaryG2Derived_of_prime_five (h := h) hG hM hJ e).elim
  · exact (s.not_tits_of_prime_five (h := h) hG hM hJ hu hL e).elim
  · exact (s.not_binaryTriality_of_prime_five (h := h) hG hM hJ e).elim

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

private noncomputable def trialityQuotient
    {p : ℕ} (s : d.PreExclusionSource h.normalized p)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : d.L ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) :
    (d.L ⧸ pCore 2 d.L) ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one := by
  have hc : center d.L = ⊥ := by
    apply bot_unique
    intro x hx
    have he := (centerCongr e ⟨x,hx⟩).property
    change e x ∈ center (Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) at he
    rw [Triality.Standard.binaryCarrier_center_eq_bot 1 Nat.zero_lt_one,mem_bot] at he
    exact mem_bot.mpr (e.map_eq_one_iff.mp he)
  exact ((QuotientGroup.quotientMulEquivOfEq
    ((s.ordinary hL).center_eq.symm.trans hc)).trans QuotientGroup.quotientBot).trans e

/-- The genuine triality cubic-action theorem identifies the original local
residual; the prime-three source action then proves its escape from M_L. -/
theorem PreExclusionSource.triality_localThreeResidual_escape
    (s : d.PreExclusionSource h.normalized 3)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : d.L ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) :
    ¬ d.localThreeResidual ≤ d.ML := by
  let := s.quasisimple
  have he := (d.source_triality_cubic_component hG h (trialityQuotient (h := h) s hL e)).2
  intro hh
  apply s.threeResidual_not_le_MZ (h := h)
  rw [he]
  exact hh.trans inf_le_left

/-- The literal residual-centralizer clause of ordinary row (4) for genuine
binary triality holds before exchanged selection, at either original prime. -/
theorem PreExclusionSource.triality_ordinaryCentralizerIdentity
    {p : ℕ} (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : d.L ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) :
    d.OrdinaryCentralizerIdentity := by
  rcases hp with rfl | rfl
  · exact (s.binaryRankTwo_model_control (h := h) hM.1.2 hu hL (.inr (.inr ⟨e⟩))).2
      (s.triality_localThreeResidual_escape (h := h) hG hL e)
  · exact (s.not_binaryTriality_of_prime_five (h := h) hG hM hJ e).elim

/-- Only the two triality parabolic identifications remain in ordinary
row (4); its original prime and residual-centralizer clause are proved. -/
theorem PreExclusionSource.ordinary22_or_triality_geometry
    {p : ℕ} (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hm : OrdinaryBinaryRankTwo d.L) :
    d.Ordinary22Alternatives ∨
      (Nonempty (d.L ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) ∧
        p = 3 ∧ d.OrdinaryCentralizerIdentity) := by
  unfold OrdinaryBinaryRankTwo at hm
  rcases hm with he | he | he <;> obtain ⟨e⟩ := he
  · exact .inl (s.ordinary22_of_binaryG2Derived (h := h) hp hG hM hJ hu hL e)
  · exact .inl (s.ordinary22_of_tits (h := h) hp hG hM hJ hu hL e)
  · exact .inr ⟨⟨e⟩,s.prime_three_of_binaryRankTwo (h := h) hp hG hM hJ hu hL (.inr (.inr ⟨e⟩)),
      s.triality_ordinaryCentralizerIdentity (h := h) hp hG hM hJ hu hL e⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Apply the complete Tits row and the original binary rank-two prime and
centralizer reductions at the same marker, component, Z₁ and source row. -/
theorem PreparedChosenModule.source_preExclusion_rankTwo_refinement
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
        (Nonempty (d.L ≃* Tits.ParrottGroup) → d.Ordinary22Alternatives) ∧
        (CaseIComponentData.OrdinaryBinaryRankTwo d.L → m.prime = 3 ∧
          (d.Ordinary22Alternatives ∨
            (Nonempty (d.L ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) ∧
              d.OrdinaryCentralizerIdentity)))) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,fun hL => ⟨?_,?_⟩⟩
  · rintro ⟨e⟩
    exact s.ordinary22_of_tits (h := h) hp hG hM hJ hu hL e
  · intro hm
    refine ⟨s.prime_three_of_binaryRankTwo (h := h) hp hG hM hJ hu hL hm,?_⟩
    rcases s.ordinary22_or_triality_geometry (h := h) hp hG hM hJ hu hL hm with he | ⟨he,_,hc⟩
    · exact .inl he
    · exact .inr ⟨he,hc⟩

end CFSG.Quasithin.Chapter15.Section01
