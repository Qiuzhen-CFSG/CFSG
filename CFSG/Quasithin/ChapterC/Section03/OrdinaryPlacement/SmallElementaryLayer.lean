module
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SourcePlacement
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.A5ActionRank
public import Stellmacher.OmegaOneCenterMap
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse
public import Theory.ElementaryAbelian.Quotient
public import Theory.GroupTheory.PrimeRankSquareFree

/-!
# Small elementary layers in the ordinary C.3 component

The original C.2.8 module lies in Ω₁Z(O₂(X)), where X is its component
span. This elementary subgroup is preserved by all of M. Its image in the
ordinary component modulo its center therefore carries the literal M-action.
The source commutator identity makes the X-action nontrivial. If the original
A₅ component were nonnormal, the pair action kernel would be a two-group and
the action image would have five-rank at least two. In dimension at most seven,
the binary general linear group has five-rank at most one.

This gives the specialized A₅ consequence of the finite ordinary rows in
Aschbacher–Smith C.3.1, printed p.151, from their intrinsic two-rank bounds.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.HypothesisC28
universe u v
variable {G : Type u} [Group G] [Finite G] {H M L R V : Subgroup G}
variable {κ : GroupClass.{u}}

private theorem small_elementary_automorphism_five_rank
    (E : Type*) [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hc : Nat.card E ≤ 2 ^ 7) : primeRank 5 (MulAut E) ≤ 1 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply primeRank_le_one_of_square_not_dvd
  obtain ⟨d, hd⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  have hdim : d ≤ 7 := by
    rw [hd] at hc
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc
  rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow E d hd]
  interval_cases d <;> norm_num [Fin.prod_univ_succ]

theorem a5_nonnormal_span_hom_odd_rank
    (h : HypothesisC28 κ H M L R V)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
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
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let ae := subgroupOfEquivOfLe h.component_le
  let : IsSimpleGroup (A ⧸ pCore 2 A) :=
    ((QuotientGroup.congr _ _ ae (pCore_map_iso 2 ae)).trans e).isSimpleGroup
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

/-- A small elementary layer in the actual ordinary component quotient forces
normality of the original A₅ component. -/
theorem normalizes_a5_of_ordinary_quotient_twoRank_le_seven
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) (hK : IsComponent H K)
    (hr : primeRank 2 (K ⧸ center K) ≤ 7) :
    M ≤ normalizer (L : Set G) := by
  by_contra hn
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
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
  have hlarge : 2 ≤ primeRank 5 ((X.subgroupOf M).map f) := by
    rw [h.a5_nonnormal_span_hom_odd_rank a hn f hne (by decide : Odd 5)]
    exact h.two_le_span_fiveRank_of_a5_nonnormal a hn
  have hsmall : primeRank 5 ((X.subgroupOf M).map f) ≤ 1 :=
    (primeRank_subgroup_le _ _).trans (small_elementary_automorphism_five_rank E hEcard)
  omega

end CFSG.Quasithin.ChapterC.HypothesisC28
