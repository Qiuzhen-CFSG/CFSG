module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.OrdinaryLayer
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Bounds
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.FiniteClosure

/-!
# J₄ exclusions on the original elementary-layer and full-module actions

In the covering configuration, a nontrivial action of the perfect conjugate
span retains the doubled odd ranks of the centerless seed. Its elementary
layer modulo the full component center embeds in the J₄ quotient. The native
two-rank bound makes the automorphism group of this layer have eleven-rank at
most one; the native J₄ order bounds every other odd rank except three.
Burnside's theorem supplies a contradictory odd prime different from three.

For an odd-actor normalizer with trivial two-core, the original full module
injects through the component's central quotient. Its actual local action has
two-group kernel, giving the same contradiction. Native outer solvability
supplies residual placement under covering uniqueness. The final application
uses the literal intersection of the Hall image with the section centralizer.

Source: Aschbacher--Smith C.3.5, 4.4.6--12 and 10.2.3(2),
printed pp.150,620--623,745. The full component centers are retained.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.HypothesisC28
universe u
variable {G : Type u} [Group G] [Finite G] {H M L R V : Subgroup G}

private theorem covering_elementary_layer (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V) :
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

/-- The actual elementary layer detects any doubled odd prime rank of the
centerless seed, retaining the full ordinary component center. -/
theorem normalizes_of_simple_ordinary_layer_prime
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    [IsQuasisimple (L ⧸ pCore 2 L)] (hz : center (L ⧸ pCore 2 L) = ⊥)
    (K : Subgroup H) (hK : IsComponent H K)
    {d p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hd : p ∣ Nat.card (L ⧸ pCore 2 L))
    (hr : primeRank 2 (K ⧸ center K) ≤ d)
    (hAut : ∀ (E : Type u) [Group E] [Finite E] [IsElementaryAbelian 2 E],
      Nat.card E ≤ 2 ^ d → primeRank p (MulAut E) ≤ 1) :
    M ≤ normalizer (L : Set G) := by
  by_contra hn
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsSimpleGroup ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) := IsQuasisimple.simple
  let : IsSimpleGroup (L ⧸ pCore 2 L) :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  have hpos : 0 < primeRank p (L ⧸ pCore 2 L) := by
    have hh : primeRank p (L ⧸ pCore 2 L) ≠ 0 :=
      fun he => PrimeRank.eq_zero_iff_not_dvd_card.mp he hd
    omega
  let := h.ordinary_component_normal K hK
  obtain ⟨W,hWe,hVW,hWX,hMW⟩ := covering_elementary_layer h
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
  have hEcard : Nat.card E ≤ 2 ^ d := by
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
    (primeRank_subgroup_le _ _).trans (hAut E hEcard)
  omega

private theorem eleven_rank_small_elementary_aut
    (E : Type*) [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hc : Nat.card E ≤ 2 ^ 11) : primeRank 11 (MulAut E) ≤ 1 := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  apply primeRank_le_one_of_square_not_dvd
  obtain ⟨d,hd⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  have hdim : d ≤ 11 := by
    rw [hd] at hc
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc
  rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow E d hd]
  interval_cases d <;> norm_num [Fin.prod_univ_succ]

private theorem janko_odd_rank
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hp3 : p ≠ 3) (hp11 : p ≠ 11) :
    primeRank p Janko4.Model ≤ 1 := by
  apply primeRank_le_one_of_square_not_dvd
  rw [Janko4.Cardinality.model_card]
  intro hs
  have hp : p.Prime := Fact.out
  have h2 : Nat.Coprime p 2 := hp.coprime_iff_not_dvd.mpr (by
    intro hd
    have he := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd
    subst p
    exact ho.not_two_dvd_nat (dvd_refl 2))
  have h3 : Nat.Coprime p 3 := hp.coprime_iff_not_dvd.mpr
    (fun hd => hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hd))
  have h11 : Nat.Coprime p 11 := hp.coprime_iff_not_dvd.mpr
    (fun hd => hp11 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp hd))
  have hc : Nat.Coprime (p ^ 2) (2 ^ 21 * 3 ^ 3 * 11 ^ 3) :=
    (((h2.pow_right 21).mul_right (h3.pow_right 3)).mul_right (h11.pow_right 3)).pow_left 2
  have hd : p ^ 2 ∣ 2 ^ 21 * 3 ^ 3 * 11 ^ 3 * (5 * 7 * 23 * 29 * 31 * 37 * 43) := by
    convert hs using 1
    norm_num
  have hsf : Squarefree (5 * 7 * 23 * 29 * 31 * 37 * 43 : ℕ) := by
    have h0 : Squarefree (5 : ℕ) := (Nat.prime_iff.mp (by decide : Nat.Prime 5)).squarefree
    have h1 : Squarefree (5 * 7 : ℕ) :=
      (Nat.squarefree_mul (by decide : Nat.Coprime (5) 7)).mpr
        ⟨h0, (Nat.prime_iff.mp (by decide : Nat.Prime 7)).squarefree⟩
    have h2 : Squarefree (5 * 7 * 23 : ℕ) :=
      (Nat.squarefree_mul (by decide : Nat.Coprime (5 * 7) 23)).mpr
        ⟨h1, (Nat.prime_iff.mp (by decide : Nat.Prime 23)).squarefree⟩
    have h3 : Squarefree (5 * 7 * 23 * 29 : ℕ) :=
      (Nat.squarefree_mul (by decide : Nat.Coprime (5 * 7 * 23) 29)).mpr
        ⟨h2, (Nat.prime_iff.mp (by decide : Nat.Prime 29)).squarefree⟩
    have h4 : Squarefree (5 * 7 * 23 * 29 * 31 : ℕ) :=
      (Nat.squarefree_mul (by decide : Nat.Coprime (5 * 7 * 23 * 29) 31)).mpr
        ⟨h3, (Nat.prime_iff.mp (by decide : Nat.Prime 31)).squarefree⟩
    have h5 : Squarefree (5 * 7 * 23 * 29 * 31 * 37 : ℕ) :=
      (Nat.squarefree_mul (by decide : Nat.Coprime (5 * 7 * 23 * 29 * 31) 37)).mpr
        ⟨h4, (Nat.prime_iff.mp (by decide : Nat.Prime 37)).squarefree⟩
    have h6 : Squarefree (5 * 7 * 23 * 29 * 31 * 37 * 43 : ℕ) :=
      (Nat.squarefree_mul (by decide : Nat.Coprime (5 * 7 * 23 * 29 * 31 * 37) 43)).mpr
        ⟨h5, (Nat.prime_iff.mp (by decide : Nat.Prime 43)).squarefree⟩
    exact h6
  exact (Nat.squarefree_iff_prime_squarefree.mp hsf p hp)
    (by simpa only [pow_two] using hc.dvd_mul_left.mp hd)

/-- The actual J₄ two-rank bound and native order rule out the doubled
odd ranks of the centerless nonnormal seed on its elementary layer. -/
theorem normalizes_of_simple_ordinary_jankoFour
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    [IsQuasisimple (L ⧸ pCore 2 L)] (hz : center (L ⧸ pCore 2 L) = ⊥)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : K ⧸ center K ≃* Janko4.Model) : M ≤ normalizer (L : Set G) := by
  let : IsSimpleGroup ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) := IsQuasisimple.simple
  let : Nontrivial (L ⧸ pCore 2 L) :=
    (QuotientGroup.mk'_surjective (center (L ⧸ pCore 2 L))).nontrivial
  obtain ⟨p,hp,ho,hp3,hd⟩ := Perfect.exists_odd_prime_ne_dvd_card
    (L ⧸ pCore 2 L) Nat.prime_three
  let : Fact p.Prime := ⟨hp⟩
  by_cases hp11 : p = 11
  · subst p
    apply h.normalizes_of_simple_ordinary_layer_prime hz K hK ho hd
      (d := 11)
    · rw [primeRank_congr 2 e]
      exact Janko4.TwoRank.model_twoRank_le_eleven
    · exact eleven_rank_small_elementary_aut
  · have hpos : 0 < primeRank p (L ⧸ pCore 2 L) := by
      have hh : primeRank p (L ⧸ pCore 2 L) ≠ 0 :=
        fun he => PrimeRank.eq_zero_iff_not_dvd_card.mp he hd
      omega
    have hsmall : primeRank p (conjugateSpanBy L M) ≤ 1 := by
      obtain ⟨_,_,_,_,hr⟩ := h.ordinary_quotient_local_data K hK
      rw [←hr p hp ho]
      apply (primeRank_subgroup_le p _).trans
      rw [primeRank_congr p e]
      exact janko_odd_rank ho hp3 hp11
    exact h.normalizes_of_span_odd_rank ho hz hpos (by omega)

end CFSG.Quasithin.ChapterC.HypothesisC28

namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The literal full-module action retains the doubled odd ranks of the
original nonnormal component, using its proved two-group kernel. -/
theorem source_nonnormal_fullModule_automorphism_rank
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (ho : Odd p) :
    2 * primeRank p (L ⧸ pCore 2 L) ≤ primeRank p (MulAut D.fullModule) := by
  let J := localJoin T L
  let V := D.fullModule
  have hJM : J ≤ D.maximalLocal :=
    sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)
  have hVJ : V ≤ J := D.fullModule_le_orbit.trans le_sup_left
  let f : J →* MulAut V := V.normalizerMonoidHom.comp
    (inclusion (hJM.trans D.maximalLocal_normalizes_fullModule))
  have he : f.ker = centralizer (V.subgroupOf J : Set J) := by
    ext j
    constructor
    · intro hj v hv
      have hh := congrArg (fun a : MulAut V => (a ⟨v,hv⟩ : G)) hj
      change (j : G) * (v : G) * (j : G)⁻¹ = v at hh
      exact Subtype.ext (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro hj
      apply MulEquiv.ext
      intro v
      apply Subtype.ext
      have hh := congrArg Subtype.val (hj ⟨v,hVJ v.property⟩ v.property)
      change (v : G) * j = (j : G) * v at hh
      change (j : G) * (v : G) * (j : G)⁻¹ = v
      rw [←hh,mul_inv_cancel_right]
  have hk : IsPGroup 2 f.ker := by
    rw [he]
    exact source_nonnormal_full_module_local_kernel_isTwoGroup D hn
  let X := (localOrbit T L).subgroupOf J
  obtain ⟨e⟩ := source_nonnormal_orbit_product_equiv D hn
  have hr : primeRank p X = 2 * primeRank p (L ⧸ pCore 2 L) := by
    rw [primeRank_congr p (subgroupOfEquivOfLe (show localOrbit T L ≤ J from le_sup_left)),
      ←primeRank_quotient_eq_of_isTwoGroup p ho (pCore 2 (localOrbit T L)) pCore_isPGroup,
      primeRank_congr p e,primeRank_prod_eq_add,two_mul]
  rw [←hr,←ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel ho f hk X]
  exact primeRank_subgroup_le p _

private theorem elementary_card_le_of_core_zero
    {K : Type*} [Group K] [Finite K] (W : Subgroup K)
    (hW : IsElementaryAbelian 2 W) (hc : pCore 2 K = ⊥)
    {d : ℕ} (hr : primeRank 2 (K ⧸ center K) ≤ d) : Nat.card W ≤ 2 ^ d :=
  elementary_card_le_of_twoCore_eq_bot W hW hc hr

/-- The J₄ row is excluded on the actual full module in the zero-two-core
normalizer branch. Its full component center and original residual are retained. -/
theorem source_nonnormal_oddNormalizer_no_placed_jankoFour_component
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G))) (hc : pCore 2 K = ⊥)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K)
    (e : K ⧸ center K ≃* Janko4.Model) : False := by
  let S := L ⧸ pCore 2 L
  let := D.quasisimple
  let : IsSimpleGroup (S ⧸ center S) := IsQuasisimple.simple
  let : Nontrivial S := (QuotientGroup.mk'_surjective (center S)).nontrivial
  obtain ⟨p,hp,ho,hp3,hd⟩ := Perfect.exists_odd_prime_ne_dvd_card S Nat.prime_three
  let : Fact p.Prime := ⟨hp⟩
  have hpos : 0 < primeRank p S := by
    have hne : primeRank p S ≠ 0 := fun hh => PrimeRank.eq_zero_iff_not_dvd_card.mp hh hd
    omega
  by_cases hp11 : p = 11
  · subst p
    let N := normalizer (B : Set G)
    let F := (solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype
    let W := (D.fullModule.subgroupOf N).subgroupOf K
    have hVN : D.fullModule ≤ N := (le_centralizer_iff.mp hBV).trans (Subgroup.centralizer_le_normalizer _)
    have hVK : D.fullModule.subgroupOf N ≤ K := by
      obtain ⟨_,_,hVF⟩ := source_fullModule_oddActor_cover D B hBC hodd hBV
      exact (subgroupOf_mono N (hVF.trans (pCoreIn_le 2 F))).trans hFK
    obtain ⟨_,_,_,_,hW,_,_,_,_⟩ :=
      source_oddNormalizer_component_local_geometry_of_residual_le D B hBC hodd hBV K hFK
    have hcard : Nat.card D.fullModule ≤ 2 ^ 11 := by
      rw [←Nat.card_congr ((subgroupOfEquivOfLe hVK).trans (subgroupOfEquivOfLe hVN)).toEquiv]
      exact elementary_card_le_of_core_zero W hW hc
        ((primeRank_congr 2 e).trans_le Janko4.TwoRank.model_twoRank_le_eleven)
    let := D.fullModule_elementary (Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
      (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
      (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
      D.simpleQTKE T D.maximal)
    have hlo := source_nonnormal_fullModule_automorphism_rank D hn ho
    change 2 * primeRank 11 S ≤ primeRank 11 (MulAut D.fullModule) at hlo
    have hup := ChapterC.HypothesisC28.eleven_rank_small_elementary_aut D.fullModule hcard
    omega
  · obtain ⟨_,_,_,_,_,hr⟩ :=
      source_nonnormal_oddNormalizer_component_quotient_geometry D hn B hBC hodd hBV K hFK
    have hlo : 2 * primeRank p S ≤ primeRank p (K ⧸ center K) :=
      (hr p hp ho).symm.le.trans (primeRank_subgroup_le p _)
    have hup : primeRank p (K ⧸ center K) ≤ 1 := by
      rw [primeRank_congr p e]
      exact ChapterC.HypothesisC28.janko_odd_rank ho hp3 hp11
    omega
/-- Native outer solvability supplies placement of the original residual
in the J₄ component once covering uniqueness is available. -/
theorem source_nonnormal_oddNormalizer_no_jankoFour_component
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hu : UniqueMaximalOvergroup
      ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype ⊔
        ((T : Subgroup G) ⊓ normalizer (B : Set G))) D.maximalLocal)
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K) [K.Normal]
    (hout : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hc : pCore 2 K = ⊥) (e : K ⧸ center K ≃* Janko4.Model) : False := by
  exact source_nonnormal_oddNormalizer_no_placed_jankoFour_component D hn B hBC hodd hBV K hc
    (source_nonnormal_oddNormalizer_residual_le_of_theoremC D hn B hBC hodd hBV hu K hK hout
      (.sporadic (Or.inl ⟨.j4, (by intro h; cases h), ⟨e⟩⟩))) e

/-- The literal elementary Hall-kernel application of the J₄ exclusion.
Only the earlier module fixation and covering uniqueness remain explicit. -/
theorem source_hall_kernel_no_jankoFour_component
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (Y : Subgroup H)
    (hfix : Y.map H.subtype ⊓ sectionCentralizer (localOrbit T L) ≤
      centralizer (D.fullModule : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (A : Subgroup G) (hA : IsElementaryAbelian p A)
    (hAY : A ≤ Y.map H.subtype) (hAC : A ≤ sectionCentralizer (localOrbit T L))
    (hu : UniqueMaximalOvergroup
      ((solvableResidual (localOrbit T L ⊓ centralizer (A : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (A : Set G)).subtype ⊔
        ((T : Subgroup G) ⊓ normalizer (A : Set G))) D.maximalLocal)
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K) [K.Normal]
    (hout : ¬ K.map (normalizer (A : Set G)).subtype ≤ D.maximalLocal)
    (hc : pCore 2 K = ⊥) (e : K ⧸ center K ≃* Janko4.Model) : False := by
  let := hA
  have ho : Odd (Nat.card A) := by
    obtain ⟨n,he⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [he]
    exact hp.pow
  exact source_nonnormal_oddNormalizer_no_jankoFour_component D hn A hAC ho
    ((le_inf hAY hAC).trans hfix) hu K hK hout hc e

end CFSG.Quasithin.Chapter10
