module
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SourceA5Normality
public import Theory.GroupTheory.PerfectPairOrder
public import Theory.GroupTheory.ElementarySmallRankBounds
public import Theory.SpecificGroups.Rudvalis.Model.Order

/-!
# The elementary layer of an ordinary covering component

The source module lies in the characteristic elementary center of the
span's two-core. Its image modulo the ordinary component center carries
a nontrivial action of the original span. A centerless nonnormal seed
makes that action preserve every odd rank. In dimension at most seven,
automorphism ranks outside three and seven are at most one. An independent
seven-rank bound therefore forces the seed to be normal.

The actual J₂, HS and Rudvalis carriers satisfy both bounds. Their
application to the original covering counterexample is in OrdinarySource.
Source: Aschbacher--Smith C.3.5 and C.4.8, pp.150--154, used by
4.2.12 and 4.4.6, pp.610,620.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.HypothesisC28
universe u v
variable {G : Type u} [Group G] [Finite G] {H M L R V : Subgroup G}
variable {κ : GroupClass.{u}}

theorem simple_nonnormal_span_hom_odd_rank
    (h : HypothesisC28 κ H M L R V)
    [IsSimpleGroup (L ⧸ pCore 2 L)]
    (hn : ¬ M ≤ normalizer (L : Set G))
    {D : Type v} [Group D] [Finite D] (f : M →* D)
    (hne : ((conjugateSpanBy L M).subgroupOf M).map f ≠ ⊥)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) :
    primeRank p (((conjugateSpanBy L M).subgroupOf M).map f) =
      primeRank p (conjugateSpanBy L M) := by
  let A := L.subgroupOf M
  let X := conjugateSpanBy A (⊤ : Subgroup M)
  let Y := conjugateSpanBy L M
  have hYM : Y ≤ M := conjugateSpanBy_le_self h.component_le
  have hmap : X.map M.subtype = Y := by
    change (conjugateSpanBy A ⊤).map M.subtype = Y
    rw [map_conjugateSpanBy, map_subgroupOf_eq_of_le h.component_le,
      ← MonoidHom.range_eq_map, range_subtype]
  have hX : X = Y.subgroupOf M := by
    apply map_injective M.subtype_injective
    rw [map_subgroupOf_eq_of_le hYM]
    exact hmap
  have hM : IsSQTK κ M :=
    (IsSQTK.equiv (subgroupOfEquivOfLe h.local_le)).mp (h.sqtk.subgroup (M.subgroupOf H))
  have hQ : IsSQTK κ (M ⧸ pCore 2 M) := by
    refine ⟨?_, hM.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hM.stronglyQuasithin p hp ho)
  have hi : (normalizer (A : Set M)).index = 2 := by
    rcases Chapter1.Section02.proposition_1_2_1_three_orbit_source hQ h.component with hN | hi
    · let := hN
      apply (hn ?_).elim
      have hh := A.le_normalizer_map M.subtype
      simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype, A,
        map_subgroupOf_eq_of_le h.component_le] using hh
    · exact hi
  let ae := subgroupOfEquivOfLe h.component_le
  let : IsSimpleGroup (A ⧸ pCore 2 A) :=
    (QuotientGroup.congr _ _ ae (pCore_map_iso 2 ae)).isSimpleGroup
  have hh := pair_span_action_odd_rank A h.component hi f (by change X.map f ≠ ⊥; rw [hX]; exact hne) ho
  change primeRank p (X.map f) = primeRank p X at hh
  rw [hX] at hh
  exact hh.trans (primeRank_congr p (subgroupOfEquivOfLe hYM))

private theorem source_elementary_layer (h : HypothesisC28 κ H M L R V) :
    ∃ W : Subgroup G, IsElementaryAbelian 2 W ∧ V ≤ W ∧
      W ≤ conjugateSpanBy L M ∧ M ≤ normalizer (W : Set G) := by
  let X := conjugateSpanBy L M
  let C := X.pCoreIn 2
  let W := omegaOneCenterAmbient C
  have hMX : M ≤ normalizer (X : Set G) := le_normalizer_conjugateSpanBy L M
  have hMC : M ≤ normalizer (C : Set G) :=
    hMX.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  have hVC : V ≤ C := le_pCoreIn_of_normalizes h.module_elementary.isPGroup h.module_le
    (le_normalizer_iff_commutator_le_left.mpr h.module_commutator.symm.le)
  have hCR : C ≤ R := by
    rw [← h.span_join_core]
    exact pCoreIn_mono_of_normalizes le_sup_left
      (sup_le X.le_normalizer (h.radical_le.trans hMX))
  let Z := (omega₁ (center C) (p := 2)).map (center C).subtype
  let : (omega₁ (center C) (p := 2)).Characteristic := omega₁_characteristic _
  let : Z.Characteristic := inferInstance
  refine ⟨W, omegaOneCenterAmbient_elementaryAbelian C, ?_, ?_,
    hMC.trans (normalizer_le_normalizer_characteristic_image C Z)⟩
  · intro x hx
    apply (mem_omegaOneCenterAmbient_iff C x).mpr
    refine ⟨hVC hx, ?_, ?_⟩
    · let := h.module_elementary
      exact elemPow_eq_one_of_isElementaryAbelian x hx
    · intro c hc
      obtain ⟨v,hv,he⟩ := h.module_le_center_radical hx
      have hh := congrArg (fun y : R => (y : G)) ((mem_center_iff.mp hv) ⟨c,hCR hc⟩)
      change c * (v : G) = (v : G) * c at hh
      change (v : G) = x at he
      rwa [he] at hh
  · intro x hx
    exact (pCoreIn_le 2 X) ((mem_omegaOneCenterAmbient_iff C x).mp hx).1

private theorem small_elementary_automorphism_rank
    (E : Type*) [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hc : Nat.card E ≤ 2 ^ 7)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hp3 : p ≠ 3) (hp7 : p ≠ 7) :
    primeRank p (MulAut E) ≤ 1 :=
  primeRank_mulAut_le_one_of_card_le_two_pow_seven E hc ho hp3 hp7

theorem normalizes_of_simple_ordinary_small_layer
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    [IsQuasisimple (L ⧸ pCore 2 L)] (hz : center (L ⧸ pCore 2 L) = ⊥)
    (K : Subgroup H) (hK : IsComponent H K)
    (hr : primeRank 2 (K ⧸ center K) ≤ 7)
    (hr7 : primeRank 7 (K ⧸ center K) ≤ 1) :
    M ≤ normalizer (L : Set G) := by
  by_contra hn
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsSimpleGroup ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) := IsQuasisimple.simple
  let : IsSimpleGroup (L ⧸ pCore 2 L) :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  obtain ⟨p,hp,ho,hp3,hd⟩ := Perfect.exists_odd_prime_ne_dvd_card (L ⧸ pCore 2 L) Nat.prime_three
  let : Fact p.Prime := ⟨hp⟩
  have hpos : 0 < primeRank p (L ⧸ pCore 2 L) := by
    have hh : primeRank p (L ⧸ pCore 2 L) ≠ 0 :=
      fun he => PrimeRank.eq_zero_iff_not_dvd_card.mp he hd
    omega
  have hp7 : p ≠ 7 := by
    intro he
    subst p
    obtain ⟨_,_,_,_,hh⟩ := h.ordinary_quotient_local_data K hK
    have hrank : primeRank 7 (conjugateSpanBy L M) ≤ 1 := by
      rw [←hh 7 hp ho]
      exact (primeRank_subgroup_le 7 _).trans hr7
    exact hn (h.normalizes_of_span_odd_rank ho hz hpos (by omega))
  let := h.ordinary_component_normal K hK
  obtain ⟨W,hWe,hVW,hWX,hMW⟩ := source_elementary_layer h
  let := hWe
  let : CommGroup W := IsMulCommutative.instCommGroup
  let X := conjugateSpanBy L M
  have hXM : X ≤ M := conjugateSpanBy_le_self h.component_le
  have hXH : X ≤ H := hXM.trans h.local_le
  have hWH : W ≤ H := hWX.trans hXH
  have hWK : W.subgroupOf H ≤ K := (subgroupOf_mono H hWX).trans (h.ordinary_span_le K hK)
  let i : W →* K := (inclusion hWK).comp (subgroupOfEquivOfLe hWH).symm.toMonoidHom
  let ZH : Subgroup H := (center K).map K.subtype
  let Z : Subgroup G := ZH.map H.subtype
  let : ZH.Normal := inferInstance
  let : (Z.subgroupOf W).Normal := inferInstance
  have hMZ : M ≤ normalizer (Z : Set G) := by
    intro m hm
    apply ZH.le_normalizer_map H.subtype
    exact mem_map_of_mem H.subtype
      (show (⟨m,h.local_le hm⟩ : H) ∈ normalizer (ZH : Set H) from
        le_normalizer_of_normal (mem_top _))
  let q := (QuotientGroup.mk' (center K)).comp i
  have hker : Z.subgroupOf W = q.ker := by
    ext w
    change (w : G) ∈ Z ↔ QuotientGroup.mk' (center K) (i w) = 1
    constructor
    · rintro ⟨z,⟨k,hk,hkz⟩,hzw⟩
      have he : k = i w := by
        apply K.subtype_injective
        apply H.subtype_injective
        exact (congrArg (fun z : H => (z : G)) hkz).trans hzw
      exact (QuotientGroup.eq_one_iff (i w)).mpr (he ▸ hk)
    · intro hw
      exact ⟨(i w : H),⟨i w,(QuotientGroup.eq_one_iff (i w)).mp hw,rfl⟩,rfl⟩
  let E := W ⧸ Z.subgroupOf W
  let j : E →* K ⧸ center K := QuotientGroup.lift _ q hker.le
  have hj : Function.Injective j := (QuotientGroup.injective_lift_iff _ _ _).mpr hker
  let : IsElementaryAbelian 2 E := inferInstance
  have hEcard : Nat.card E ≤ 2 ^ 7 := by
    have ht : IsElementaryAbelian 2 j.range :=
      IsElementaryAbelian.of_surjective j.rangeRestrict j.rangeRestrict_surjective
    have hc := (primeRank_le_iff_elementary_card_le (K ⧸ center K)).mp hr j.range ht
    rw [Nat.card_congr (MonoidHom.ofInjective hj).toEquiv]
    exact hc
  obtain ⟨f,hf⟩ := exists_quotient_conjugation_action M W Z hMW hMZ inferInstance
  have hne : (X.subgroupOf M).map f ≠ ⊥ := by
    intro he
    have hk : X.subgroupOf M ≤ f.ker := (Subgroup.map_eq_bot_iff _).mp he
    have hcomm : ⁅W,X⁆ ≤ Z := by
      rw [commutator_comm]
      apply commutator_le.mpr
      intro x hx w hw
      have hfix := hf ⟨x,hXM hx⟩ ⟨w,hw⟩
      have hid : f ⟨x,hXM hx⟩ = 1 := hk hx
      rw [hid] at hfix
      have hmem := QuotientGroup.eq_iff_div_mem.mp hfix.symm
      change x*w*x⁻¹/w ∈ Z at hmem
      simpa only [commutatorElement_def,div_eq_mul_inv] using hmem
    have hVZ : V ≤ Z := h.module_commutator ▸ (commutator_mono hVW le_rfl).trans hcomm
    apply h.ordinary_module_not_centralizes K hK
    intro v hv k hk
    obtain ⟨z,⟨c,hc,hcz⟩,hzv⟩ := hVZ hv
    have hcv : (c : H) = v := H.subtype_injective
      ((congrArg (fun z : H => (z : G)) hcz).trans hzv)
    have hh := congrArg (fun t : K => (t : H)) ((mem_center_iff.mp hc) ⟨k,hk⟩)
    change k * (c : H) = (c : H) * k at hh
    rwa [hcv] at hh
  have hlarge : 2 ≤ primeRank p ((X.subgroupOf M).map f) := by
    rw [h.simple_nonnormal_span_hom_odd_rank hn f hne ho]
    by_contra! hh
    exact hn (h.normalizes_of_span_odd_rank ho hz hpos (by omega))
  have hsmall : primeRank p ((X.subgroupOf M).map f) ≤ 1 :=
    (primeRank_subgroup_le _ _).trans (small_elementary_automorphism_rank E hEcard ho hp3 hp7)
  omega

variable (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    [IsQuasisimple (L ⧸ pCore 2 L)] (hz : center (L ⧸ pCore 2 L) = ⊥)
    (K : Subgroup H) (hK : IsComponent H K)
include h hz hK

theorem normalizes_of_simple_ordinary_j2
    (e : K ⧸ center K ≃* Sporadic.LeechRelated.J2.Carrier) :
    M ≤ normalizer (L : Set G) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  apply h.normalizes_of_simple_ordinary_small_layer hz K hK
  · rw [primeRank_congr 2 e]
    exact Sporadic.LeechRelated.J2.primeRank_two_le_seven
  · rw [primeRank_congr 7 e]
    apply primeRank_le_one_of_square_not_dvd
    rw [Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier]
    decide

theorem normalizes_of_simple_ordinary_hs
    (e : K ⧸ center K ≃* Sporadic.LeechRelated.HS.Carrier) :
    M ≤ normalizer (L : Set G) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  apply h.normalizes_of_simple_ordinary_small_layer hz K hK
  · rw [primeRank_congr 2 e]
    exact Sporadic.LeechRelated.HS.twoRank_le_four.trans (by decide)
  · rw [primeRank_congr 7 e]
    apply primeRank_le_one_of_square_not_dvd
    rw [Sporadic.LeechRelated.HS.NormalizerIndex.card_carrier]
    decide

theorem normalizes_of_simple_ordinary_rudvalis
    (e : K ⧸ center K ≃* Rudvalis.Model) : M ≤ normalizer (L : Set G) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  apply h.normalizes_of_simple_ordinary_small_layer hz K hK
  · rw [primeRank_congr 2 e]
    exact Rudvalis.primeRank_le_six.trans (by decide)
  · rw [primeRank_congr 7 e]
    apply primeRank_le_one_of_square_not_dvd
    rw [Rudvalis.model_card]
    decide

end CFSG.Quasithin.ChapterC.HypothesisC28
