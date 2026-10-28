module
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.Source
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.CoreNormality
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.CenterBound
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.J2Source
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.PairFusion
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.SecondExchanged
public import Theory.SpecificGroups.PSL3Four.CentralCover.FieldComponentFusion

/-!
# Persistence on the original prime component's two-core

A bad core involution has the literal four-group centralizer supplied by
its dihedral core. The retained overcomponent is a marked PSL₃(4) cover,
a marked J₂ cover, or two exchanged simple components. In each case the
original fixed component fuses t with t zK, contradicting the source
nonfusion of t and z. Thus K remains a component in every core-involution
centralizer. The four-group Sylow argument then proves its normality there.

Source: Aschbacher–Smith 2.5.19(4) and 2.5.21, printed pp.561–566.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents
open ComponentRefinement ComponentSelection OvercomponentsSource PrimeRows
open _root_.CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The original prime component persists in every core-involution
centralizer, retaining the exact field and outer-action marks. -/
theorem source_prime_core_components
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    {p : ℕ} [Fact p.Prime] (hp : 7 ≤ p) (hfm : IsFermatOrMersennePrime p)
    (eK : K ≃* PSL(2,ZMod p))
    (hmodel : ∃ k : ℕ, 2 ≤ k ∧ Nonempty (twoCore H ≃* DihedralGroup (2 ^ k)))
    (t zK : G) (ht : orderOf t = 2) (hzK : orderOf zK = 2)
    (htC : t ∈ twoCore H) (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (hzKK : zK ∈ K) (hz : z = t * zK) (_hneq : z ≠ zK) :
    ∀ i ∈ twoCore H, orderOf i = 2 → IsComponentIn K (centralizer ({i} : Set G)) := by
  classical
  intro i hiC hi
  have hKt := source_component_in_centralizer_t c hG hempty hgen hb hstar t ht htC htZ
  by_cases hti : t = i
  · exact hti ▸ hKt
  by_contra hbad
  have hc := MathieuSourceSetup.core_eq_sylow_centralizer c hgen
  have hiSC : i ∈ (S : Subgroup H).map H.subtype ⊓ centralizer (K : Set G) := hc ▸ hiC
  have hKi : K ≤ centralizer ({i} : Set G) :=
    fun k hk => mem_centralizer_singleton_iff.mpr (hiSC.2 k hk)
  have hbad' : BadInvolution ((S : Subgroup H).map H.subtype) K i := ⟨hiSC,hi,hbad⟩
  obtain ⟨hfour,_,hiZ⟩ := source_prime_core_four c hG hempty hgen hb hstar hmodel
    t i ht hi hti htC hiC htZ
  have hR : ((S : Subgroup H).map H.subtype ⊓ centralizer (K : Set G)) ⊓
      centralizer ({i} : Set G) = zpowers t ⊔ zpowers i := by
    rw [←hc]
    exact hfour
  have hSyl : Chapter1.IsSylowIn 2 (zpowers t ⊔ zpowers i)
      (centralizer ({t} : Set G) ⊓ centralizer (K : Set G) ⊓ centralizer ({i} : Set G)) :=
    hfour ▸ source_prime_core_four_sylow c hG hempty hgen hb hstar hmodel
      t i ht hi hti htC hiC htZ
  have hnonfusion : ¬ IsConj t (t * zK) :=
    hz ▸ (MathieuSourceSetup.central_core_involution_centralizer c hgen t ht htC htZ).2.2.2.2
  obtain ⟨htI,hrows⟩ := source_bad_prime_rows c hG hempty hgen hb hstar
    hfm hp eK t i ht htC htZ hbad'
  let Gi := centralizer ({i} : Set G)
  let tI : Gi := ⟨t,htI⟩
  let D := K.subgroupOf Gi
  let X := componentOrbit D (oddELayer Gi)
  have hDX : D ≤ X := le_componentOrbit _ _
  have hKX : K ≤ X.map Gi.subtype := by
    intro k hk
    exact mem_map_of_mem Gi.subtype (hDX (show (⟨k,hKi hk⟩ : Gi) ∈ D from hk))
  rcases hrows with ⟨hX,hXN,hZp,a,ha,hact,hB,⟨eKB⟩,hm⟩ | ⟨J,hJ,hmove,hpair,_hZJ,⟨eJK⟩⟩
  · let : X.Normal := hXN
    let : IsQuasisimple X := hX.2
    have hnot : ¬ Nonempty (X ≃* K) := by
      rintro ⟨e⟩
      have he : D = X := eq_of_le_of_card_ge hDX (by
        rw [Nat.card_congr e.toEquiv,
          Nat.card_congr (subgroupOfEquivOfLe hKi).toEquiv])
      apply hbad
      refine ⟨hKi,?_⟩
      change IsComponent Gi D
      rw [he]
      exact hX
    have hcenter := NonfullA6.source_center_le_bad_involution c hG hempty hgen hb hstar
      t i ht htC htZ hi hiSC hiZ hR hSyl X hX hKX hZp hnot a ha hact
    have hnonfusionI := (NonfullA6.source_nonfusion_product_of_nonisomorphic_local_component
      c hG hempty hgen hb hstar t i ht htC htZ hi hiSC hiZ hR X hX hnot).2
    let B := (D.subgroupOf X).subgroupOf a.fixedSubgroup
    let w : X := ⟨⟨zK,hKi hzKK⟩,hDX hzKK⟩
    have hwfix : a w = w := (MulAut.mem_fixedSubgroup _ _).mp (hB.1 hzKK)
    let wB : B := ⟨⟨w,(MulAut.mem_fixedSubgroup _ _).mpr hwfix⟩,hzKK⟩
    have hwB : orderOf wB = 2 := by
      rw [←orderOf_coe wB,←orderOf_coe (wB : a.fixedSubgroup),
        ←orderOf_coe w,←orderOf_coe (w : Gi)]
      exact hzK
    rcases hm with ⟨F,_,_,hF,e,hfield⟩ | ⟨e,houter⟩
    · have hlin : ClassicalGroup.IsPSL (X ⧸ center X) 3 (2 ^ 2) :=
        ⟨F,inferInstance,inferInstance,by simpa using hF,⟨e⟩⟩
      obtain ⟨_,⟨eKtwo⟩,_⟩ := source_linear_quotient_field c hG hempty hgen hb
        (by decide : 0 < 2) hlin a ha _ hB.2 eKB
      let f : X →* G := Gi.subtype.comp X.subtype
      have hf : Function.Injective f := Gi.subtype_injective.comp X.subtype_injective
      have hpow : ∀ q ∈ center X, q ^ 2 = 1 := by
        intro q hq
        apply hf
        have hqI := hcenter (mem_map_of_mem f hq)
        have hpw := pow_card_eq_one' (x := (⟨f q,hqI⟩ : zpowers i))
        rw [Nat.card_zpowers,hi] at hpw
        have hh : (f q) ^ 2 = 1 := congrArg Subtype.val hpw
        simpa only [map_pow,map_one] using hh
      have hcard : Nat.card (center X) ≤ 2 := by
        have hh := card_le_of_le hcenter
        rw [card_map_of_injective hf,Nat.card_zpowers,hi] at hh
        exact hh
      obtain ⟨v,hv⟩ := Matrix.PSL3Four.FieldComponentFusion.ambient_fusion_of_center_quotient
        hF f e hpow hcard a (ha ▸ pow_orderOf_eq_one a) hfield B
        (eKB.symm.trans eKtwo) wB hwB t hact
      exact hnonfusion (isConj_iff.mpr ⟨f v,hv⟩)
    · have htNX : tI ∈ normalizer (X : Set Gi) := by simp only [normalizer_eq_top,mem_top]
      have hae : X.normalizerMonoidHom ⟨tI,htNX⟩ = a := by
        apply MulEquiv.ext
        intro q
        apply Subtype.ext
        apply Subtype.ext
        exact (hact q).symm
      let iI : Gi := ⟨i,mem_centralizer_singleton_iff.mpr rfl⟩
      have hiI : orderOf iI = 2 := (orderOf_coe iI).symm.trans hi
      have htI2 : orderOf tI = 2 := (orderOf_coe tI).symm.trans ht
      have hcenterI : (center X).map X.subtype ≤ zpowers iI := by
        apply (map_le_map_iff_of_injective Gi.subtype_injective).mp
        simpa only [map_map,MonoidHom.map_zpowers,Gi,iI,coe_subtype] using hcenter
      have hout : ¬ ∃ y : Sporadic.LeechRelated.J2.Carrier,
          MulAut.centralQuotientAction e (X.normalizerMonoidHom ⟨tI,htNX⟩) = MulAut.conj y := by
        rintro ⟨y,hy⟩
        rw [hae] at hy
        change MulAut.congr e (quotientAut (center X) a) = MulAut.conj y at hy
        apply houter (e.symm y)
        apply (MulAut.congr e).injective
        simpa only [MulAut.congr_conj,e.apply_symm_apply] using hy
      have hnotI : ¬ IsConj tI (tI * iI) := by
        intro hh
        obtain ⟨g,hg⟩ := isConj_iff.mp hh
        exact hnonfusionI (isConj_iff.mpr ⟨(g : G),congrArg Subtype.val hg⟩)
      have hh := j2_quotient_fixed_involution_ambient_fusion X e tI iI htNX htI2 hiI
        hcenterI hout hnotI w (by rw [hae]; exact hwfix) (by
          apply Subtype.ext
          apply Subtype.ext
          exact hzK ▸ pow_orderOf_eq_one zK)
      obtain ⟨g,hg⟩ := isConj_iff.mp hh
      exact hnonfusion (isConj_iff.mpr ⟨(g : G),congrArg Subtype.val hg⟩)
  · let : IsSimpleGroup K := (MathieuSourceSetup.small_source_structure c hG hempty hgen hb).2.1
    let : IsSimpleGroup J := eJK.isSimpleGroup
    have hD := component_in_subgroup_centralizer K t hKt Gi hKi htI
    have hDP : D ≤ J ⊔ J.map (MulAut.conj tI).toMonoidHom := hDX.trans_eq hpair
    have hh := fixed_involution_fusion_of_exchanged_simple_pair tI
      (Subtype.ext (ht ▸ pow_orderOf_eq_one t)) hJ (Ne.symm hmove) hD hDP
      (⟨zK,hKi hzKK⟩ : Gi) hzKK (Subtype.ext (hzK ▸ pow_orderOf_eq_one zK))
    obtain ⟨g,hg⟩ := isConj_iff.mp hh
    exact hnonfusion (isConj_iff.mpr ⟨(g : G),congrArg Subtype.val hg⟩)

/-- Every involution centralizer of the original prime core normalizes K.
The source component persistence and four-group Sylow premises are discharged. -/
theorem source_prime_core_normalization
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    {p : ℕ} [Fact p.Prime] (hp : 7 ≤ p) (hfm : IsFermatOrMersennePrime p)
    (eK : K ≃* PSL(2,ZMod p))
    (hmodel : ∃ k : ℕ, 2 ≤ k ∧ Nonempty (twoCore H ≃* DihedralGroup (2 ^ k)))
    (t zK : G) (ht : orderOf t = 2) (hzK : orderOf zK = 2)
    (htC : t ∈ twoCore H) (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (hzKK : zK ∈ K) (hz : z = t * zK) (hneq : z ≠ zK) :
    ∀ i ∈ twoCore H, orderOf i = 2 → centralizer ({i} : Set G) ≤ normalizer (K : Set G) := by
  intro i hiC hi
  exact source_prime_core_normalization_of_component c hG hempty hgen hb hstar hmodel
    t i ht hi htC hiC htZ (source_prime_core_components c hG hempty hgen hb hstar
      hp hfm eK hmodel t zK ht hzK htC htZ hzKK hz hneq i hiC hi)
end CFSG.Quasithin.Chapter2.Section05.Overcomponents
