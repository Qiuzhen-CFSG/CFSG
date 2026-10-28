module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalFieldComponents
public import Theory.GroupTheory.GeneralizedFitting.SylowNormalizedComponent
public import Theory.Alternating.Aut
public import Theory.GroupAction.ComponentRankAction
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.CComponent.TwoCorePrimeActors

/-!
# Normality of the lifted A5 component in source 6.2.7

An order-three automorphism of A5 is inner. Two distinct A5 components
commute, have trivial intersection, and contribute three-rank two.
A cubic normalizing both is therefore in their product: after removing its
inner actions it centralizes their product, whose centralizer has order
prime to three by the ambient rank bound.

Apply this in the actual two-core quotient of N_G(U). The component orbit
has length at most two, so the original cubic normalizes each component.
If the A5 component had a distinct conjugate, the cubic would lie in their
product inside the image of C_G(U). Odd-order membership lifts through
the two-core, contradicting the original cubic's action on U. Thus the
embedded C-component is normal in N_G(U), and in C_G(U).

The Chapter12 companion applies this to the same lifted moved component,
retaining its original quotient marking and Sylow-normalizer escapes.
This is the normality input from 6.2.4(6) used in the final paragraph of
6.2.7; the cubic centralization and field-automorphism contradiction remain.
Source: Aschbacher--Smith, printed pp.680,684, using A.3.18, pp.51--52.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]

private theorem five_center {X : Type*} [Group X]
    (e : X ≃* alternatingGroup (Fin 5)) : center X = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  apply e.injective
  have he : e x = 1 := (alternatingGroup.center_eq_bot (by simp)).le
    ((centerCongr e) ⟨x,hx⟩).property
  simpa only [map_one] using he

private theorem five_cubic_inner {X : Type*} [Group X]
    (e : X ≃* alternatingGroup (Fin 5)) (a : MulAut X) (ha : a^3=1) :
    ∃ x : X, x^3=1 ∧ MulAut.conj x = a := by
  let E : Equiv.Perm (Fin 5) ≃* MulAut (alternatingGroup (Fin 5)) :=
    MulEquiv.ofBijective MulAut.conjNormal
      (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by decide) (by decide))
  let b := MulAut.congr e a
  let s := E.symm b
  have hs : s^3=1 := by
    change (E.symm (MulAut.congr e a))^3=1
    rw [←map_pow,←map_pow,ha,map_one,map_one]
  have heven : s ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    have hsign : s.sign^3=1 := by rw [←map_pow,hs,map_one]
    rcases Int.units_eq_one_or s.sign with h | h
    · exact h
    · rw [h] at hsign
      norm_num at hsign
  let x := e.symm ⟨s,heven⟩
  have hx : MulAut.conj x = a := by
    apply (MulAut.congr e).injective
    rw [MulAut.congr_conj]
    change MulAut.conj (e (e.symm ⟨s,heven⟩)) = b
    rw [e.apply_symm_apply]
    exact MulAut.conjNormal_val.symm.trans (E.apply_symm_apply b)
  refine ⟨x,?_,hx⟩
  apply MulAut.conj_injective_of_center_eq_bot (five_center e)
  rw [map_pow,hx,ha,map_one]

private theorem five_rank {X : Type*} [Group X] [Finite X]
    (e : X ≃* alternatingGroup (Fin 5)) : 1 ≤ primeRank 3 X := by
  have hc : Nat.card X = 60 := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hn : primeRank 3 X ≠ 0 := by
    intro hz
    have hh := PrimeRank.eq_zero_iff_not_dvd_card.mp hz
    rw [hc] at hh
    exact hh (by decide)
  omega

private theorem five_pair_cubic_mem
    (B C : Subgroup G) (hB : IsComponent G B) (hC : IsComponent G C)
    (eB : B ≃* alternatingGroup (Fin 5)) (eC : C ≃* alternatingGroup (Fin 5))
    (hne : B ≠ C) (hr : primeRank 3 G ≤ 2)
    (d : G) (hd : d^3=1)
    (hdB : d ∈ normalizer (B : Set G)) (hdC : d ∈ normalizer (C : Set G)) :
    d ∈ B ⊔ C := by
  have hBC : B ≤ centralizer (C : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (hB.commutator_eq_bot_of_ne hC hne)
  have hdis : Disjoint B C := by
    apply disjoint_def.mpr
    intro x hxB hxC
    have hx : (⟨x,hxB⟩ : B) ∈ center B := mem_center_iff.mpr fun y =>
      Subtype.ext (hBC y.property x hxC).symm
    exact congrArg Subtype.val (show (⟨x,hxB⟩ : B)=1 from (five_center eB).le hx)
  let P := B ⊔ C
  have hp : 2 ≤ primeRank 3 P := by
    rw [B.primeRank_sup_eq_add_of_disjoint_commuting C hdis hBC 3]
    have := five_rank eB
    have := five_rank eC
    omega
  have hz : center P = ⊥ := by
    obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting B C hdis hBC
    apply le_bot_iff.mp
    intro x hx
    have hf := ((centerCongr e).symm ⟨x,hx⟩).property
    have hfst : (e.symm x).1 ∈ center B := mem_center_iff.mpr fun b =>
      congrArg Prod.fst (mem_center_iff.mp hf (b,1))
    have hsnd : (e.symm x).2 ∈ center C := mem_center_iff.mpr fun c =>
      congrArg Prod.snd (mem_center_iff.mp hf (1,c))
    apply e.symm.injective
    rw [map_one]
    exact Prod.ext ((five_center eB).le hfst) ((five_center eC).le hsnd)
  have hcop : Nat.Coprime 3 (Nat.card (centralizer (P : Set G))) :=
    Theory.GroupAction.ComponentRankAction.centralizer_coprime P
      (by rw [hz,card_bot]; decide) hp hr
  let a := B.normalizerMonoidHom ⟨d,hdB⟩
  let b := C.normalizerMonoidHom ⟨d,hdC⟩
  have ha : a^3=1 := by
    rw [←map_pow,show (⟨d,hdB⟩ : normalizer (B : Set G))^3=1 from Subtype.ext hd,map_one]
  have hb : b^3=1 := by
    rw [←map_pow,show (⟨d,hdC⟩ : normalizer (C : Set G))^3=1 from Subtype.ext hd,map_one]
  obtain ⟨x,hx,hxa⟩ := five_cubic_inner eB a ha
  obtain ⟨y,hy,hyb⟩ := five_cubic_inner eC b hb
  have hxy : Commute (x : G) (y : G) := (hBC x.property y y.property).symm
  have hdx : Commute d (x : G) := by
    have hh := congrArg Subtype.val (MulEquiv.congr_fun hxa x)
    change (x : G)*(x : G)*(x : G)⁻¹ = d*(x : G)*d⁻¹ at hh
    have hh' : d*(x : G)*d⁻¹ = x := by simpa only [mul_inv_cancel_right] using hh.symm
    exact mul_inv_eq_iff_eq_mul.mp hh'
  have hdy : Commute d (y : G) := by
    have hh := congrArg Subtype.val (MulEquiv.congr_fun hyb y)
    change (y : G)*(y : G)*(y : G)⁻¹ = d*(y : G)*d⁻¹ at hh
    have hh' : d*(y : G)*d⁻¹ = y := by simpa only [mul_inv_cancel_right] using hh.symm
    exact mul_inv_eq_iff_eq_mul.mp hh'
  let z := ((x : G)*(y : G))⁻¹*d
  have hzp : z^3=1 := by
    rw [(hdx.mul_right hdy).symm.inv_left.mul_pow,inv_pow,hxy.mul_pow]
    have hx' : (x : G)^3=1 := congrArg Subtype.val hx
    have hy' : (y : G)^3=1 := congrArg Subtype.val hy
    rw [hx',hy',hd,one_mul,inv_one,one_mul]
  have hzC : z ∈ centralizer (P : Set G) := by
    have hBfix : B ≤ centralizer ({z} : Set G) := by
      intro t ht
      apply mem_centralizer_singleton_iff.mpr
      have hh := congrArg Subtype.val (MulEquiv.congr_fun hxa ⟨t,ht⟩)
      change (x : G)*t*(x : G)⁻¹ = d*t*d⁻¹ at hh
      have hyT : Commute (y : G) t := (hBC ht y y.property)
      apply (mul_inv_eq_iff_eq_mul.mp (show z*t*z⁻¹=t from ?_)).symm
      calc
        _ = (y : G)⁻¹*((x : G)⁻¹*(d*t*d⁻¹)*(x : G))*(y : G) := by dsimp [z]; group
        _ = (y : G)⁻¹*t*(y : G) := by rw [←hh]; group
        _ = t := by rw [hyT.inv_left.eq,inv_mul_cancel_right]
    have hCfix : C ≤ centralizer ({z} : Set G) := by
      intro t ht
      apply mem_centralizer_singleton_iff.mpr
      have hh := congrArg Subtype.val (MulEquiv.congr_fun hyb ⟨t,ht⟩)
      change (y : G)*t*(y : G)⁻¹ = d*t*d⁻¹ at hh
      have hxT : Commute (x : G) t := (hBC x.property t ht).symm
      apply (mul_inv_eq_iff_eq_mul.mp (show z*t*z⁻¹=t from ?_)).symm
      calc
        _ = (x : G)⁻¹*((y : G)⁻¹*(d*t*d⁻¹)*(y : G))*(x : G) := by
          dsimp [z]
          rw [hxy.eq]
          group
        _ = (x : G)⁻¹*t*(x : G) := by rw [←hh]; group
        _ = t := by rw [hxT.inv_left.eq,inv_mul_cancel_right]
    intro t ht
    exact mem_centralizer_singleton_iff.mp ((sup_le hBfix hCfix) ht)
  have hz1 : z=1 := by
    have hz' : (⟨z,hzC⟩ : centralizer (P : Set G))^3=1 := Subtype.ext hzp
    have he : (⟨z,hzC⟩ : centralizer (P : Set G))=1 :=
      (powCoprime hcop.symm).injective (by
        change (⟨z,hzC⟩ : centralizer (P : Set G))^3=1^3
        simpa only [one_pow] using hz')
    exact congrArg Subtype.val he
  have he : d=(x : G)*(y : G) := (inv_mul_eq_one.mp hz1).symm
  rw [he]
  exact mul_mem (mem_sup_left x.property) (mem_sup_right y.property)


private theorem five_component_normal_of_external_cubic
    (H K : Subgroup G) [H.Normal] (hKH : K ≤ H) (hK : K.IsCComponent)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (hr : ∀ p : ℕ, p.Prime → Odd p → primeRank p G ≤ 2)
    (d : G) (hd : orderOf d=3) (hdH : d ∉ H) : K.Normal := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let B := K.map q
  let : Group.IsNilpotent (pCore 2 G) := pCore_isNilpotent
  let eB : B ≃* alternatingGroup (Fin 5) :=
    (cComponentTwoCoreQuotientEquiv hK).symm.trans eK
  let : IsSimpleGroup B := eB.isSimpleGroup
  let := (hK.map_quotient (pCore 2 G)).perfect
  let : IsQuasisimple B := {
    toIsPerfect := inferInstance
    simple := ((QuotientGroup.quotientMulEquivOfEq (five_center eB)).trans
      QuotientGroup.quotientBot).isSimpleGroup }
  have hB : IsComponent (G ⧸ pCore 2 G) B :=
    ⟨hK.subnormal.map (QuotientGroup.mk'_surjective _),inferInstance⟩
  have hrq (p : ℕ) (hp : p.Prime) (ho : Odd p) :
      primeRank p (G ⧸ pCore 2 G) ≤ 2 := by
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans (hr p hp ho)
  have hBnorm : B.Normal := by
    by_contra hn
    obtain ⟨g,hg⟩ : ∃ g : G ⧸ pCore 2 G, B.map (MulAut.conj g).toMonoidHom ≠ B := by
      by_contra! hall
      exact hn (normal_iff_map_conj_eq.mpr hall)
    let C := B.map (MulAut.conj g).toMonoidHom
    have hC : IsComponent (G ⧸ pCore 2 G) C := hB.map_conj g
    let eC : C ≃* alternatingGroup (Fin 5) := ((MulAut.conj g).subgroupMap B).symm.trans eB
    have hd3 : (q d)^3=1 := by rw [←map_pow,←hd,pow_orderOf_eq_one,map_one]
    have hnorm (A : Subgroup (G ⧸ pCore 2 G)) (hA : IsComponent _ A) :
        q d ∈ normalizer (A : Set (G ⧸ pCore 2 G)) := by
      rcases hA.normal_or_index_two_of_odd_rank_le_two hrq with hn | hi
      · exact normalizer_eq_top_iff.mpr hn ▸ mem_top _
      · have hs := (normalizer (A : Set (G ⧸ pCore 2 G))).sq_mem_of_index_two hi (q d)
        have hc : Nat.Coprime (orderOf (q d)) 2 :=
          (by decide : Nat.Coprime 3 2).of_dvd_left (orderOf_dvd_of_pow_eq_one hd3)
        exact (zpowers_le.mpr hs) (mem_zpowers_pow_iff.mpr hc.symm)
    have hm := five_pair_cubic_mem B C hB hC eB eC hg.symm
      (hrq 3 Nat.prime_three (by decide)) (q d) hd3 (hnorm B hB) (hnorm C hC)
    have hBH : B ≤ H.map q := map_mono hKH
    let : (H.map q).Normal := (inferInstance : H.Normal).map q (QuotientGroup.mk'_surjective _)
    have hCH : C ≤ H.map q := (map_mono hBH).trans_eq
      (normal_iff_map_conj_eq.mp inferInstance g)
    exact hdH (CComponentPrimeRank.prime_actor_mem_of_twoGroup_image
      (pCore 2 G) H pCore_isPGroup (by decide) d hd ((sup_le hBH hCH) hm))
  exact cComponent_normal_of_quotient_normal hK (pCore 2 G) hBnorm

/-- Every lifted A5 component embeds normally in the full field-plane normalizer.
The outside cubic excludes a pair of conjugate components, using the actual
two-core quotient and the ambient odd-prime-rank bound. -/
theorem local_field_five_component_normalizer
    {T : Sylow 2 G} {L M R U : Subgroup G} {n : ℕ}
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hfield : IsInvolutoryFieldFixedSpace L M (layer L R) U n)
    (hUc : Nat.card U=4)
    (K : Subgroup (centralizer (U : Set G))) (hK : K.IsCComponent)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) :
    (K.map (inclusion (Subgroup.centralizer_le_normalizer (U : Set G)))).Normal := by
  let H := centralizer (U : Set G)
  let N := normalizer (U : Set G)
  have hHN : H ≤ N := Subgroup.centralizer_le_normalizer _
  let j : H →* N := inclusion hHN
  let K0 := K.map j
  let H0 := H.subgroupOf N
  let : H0.Normal := normal_subgroupOf_of_le_normalizer (normalizer_le_normalizer_centralizer U)
  let a : H ≃* H0 := (subgroupOfEquivOfLe hHN).symm
  have hK0 : K0.IsCComponent := by
    have hh := (hK.map_equiv a).map_subtype (inferInstance : H0.Normal).isSubnormal
    rw [map_map] at hh
    exact hh
  let f : K ≃* K0 := K.equivMapOfInjective j (inclusion_injective _)
  let eq : (K ⧸ pCore 2 K) ≃* (K0 ⧸ pCore 2 K0) :=
    QuotientGroup.congr _ _ f (pCore_map_iso 2 f)
  have hKH : K0 ≤ H0 := by
    rintro _ ⟨k,hk,rfl⟩
    exact k.property
  have hUne : U ≠ ⊥ := by intro he; rw [he,card_bot] at hUc; contradiction
  have hN := local_field_normalizer_sqtk h hfield hUne
  obtain ⟨d,hd,ho,hdN,hdH⟩ := field_plane_cubic_outside_centralizer hnat hfield hUc
  have hnorm : K0.Normal := five_component_normal_of_external_cubic H0 K0 hKH hK0
    (eq.symm.trans e) hN.stronglyQuasithin ⟨d,hdN⟩
    ((Subgroup.orderOf_coe _).symm.trans ho) hdH
  exact hnorm

/-- Relative normality of the same original C-component inside C_G(U). -/
theorem local_field_five_component_normal
    {T : Sylow 2 G} {L M R U : Subgroup G} {n : ℕ}
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hfield : IsInvolutoryFieldFixedSpace L M (layer L R) U n)
    (hUc : Nat.card U=4)
    (K : Subgroup (centralizer (U : Set G))) (hK : K.IsCComponent)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) : K.Normal := by
  have hnorm := local_field_five_component_normalizer h hnat hfield hUc K hK e
  let j := inclusion (Subgroup.centralizer_le_normalizer (U : Set G))
  refine ⟨fun k hk x => ?_⟩
  have hh := hnorm.conj_mem (j k) (mem_map_of_mem j hk) (j x)
  apply (mem_map_iff_mem (show Function.Injective j from inclusion_injective _)).mp
  simpa only [map_mul,map_inv] using hh

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
