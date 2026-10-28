module
public import Theory.GroupTheory.PrimeRankNormalIntersection
public import Theory.GroupTheory.CComponent.ThreeResidual
public import Theory.GroupTheory.PResidual.PrimeToSubnormal
public import Theory.GroupTheory.PrimeOrderLift

/-!
# The cubic residual detected by an external cubic

Let J ≤ H be normal in a group of cubic rank at most two. If J is
centerless and its outer automorphism group has order prime to three,
an order-three element outside H can be adjusted by an element of J to
centralize J. Together with a cubic in J it generates an elementary nine.
The normal-intersection rank bound makes H ∩ C(J) prime to three, so J
has index prime to three in H.

For a C-component the argument is applied in the literal ambient two-core
quotient and lifted using relative indices. Intrinsic cubic generation
then identifies the embedded prime-to-three residual of H with J.
The original-plane application is Inspection.Residual in Chapter13.

Source: Aschbacher--Smith 13.3.12, printed pp.889--890, and the elementary
centralizer/outer-action rank argument of A.3.18, pp.51--52.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem centralizing_cubic_outside
    (J H : Subgroup G) [J.Normal] (hJH : J ≤ H)
    (hz : center J = ⊥) (ho : Nat.Coprime 3 (Nat.card (MulAut.Outer J)))
    (x : G) (hx : orderOf x = 3) (hxH : x ∉ H) :
    ∃ y : G, y ∈ centralizer (J : Set G) ∧ orderOf y = 3 ∧ y ∉ H := by
  let f : G →* MulAut.Outer J :=
    (QuotientGroup.mk' (MulAut.innerSubgroup J)).comp MulAut.conjNormal
  have hfx : f x = 1 := by
    apply orderOf_eq_one_iff.mp
    have hd : orderOf (f x) ∣ 3 := hx ▸ orderOf_map_dvd f x
    exact Nat.eq_one_of_dvd_coprimes ho hd (orderOf_dvd_natCard (f x))
  have hker : f.ker = J ⊔ centralizer (J : Set G) := by
    change ((QuotientGroup.mk' (MulAut.innerSubgroup J)).comp
      (MulAut.conjNormal : G →* MulAut J)).ker = _
    rw [← MonoidHom.comap_ker,QuotientGroup.ker_mk',MulAut.conjNormal_comap_innerSubgroup]
  have hsup : x ∈ J ⊔ centralizer (J : Set G) := hker ▸ hfx
  obtain ⟨a,ha,b,hb,hab⟩ := mem_sup_of_normal_left.mp hsup
  have hc : Commute a b := hb a ha
  have hpow : a^3 * b^3 = 1 := by rw [←hc.mul_pow,hab,←hx,pow_orderOf_eq_one]
  have ha3 : a^3 ∈ centralizer (J : Set G) := by
    have he : a^3 = (b^3)⁻¹ := eq_inv_of_mul_eq_one_left hpow
    rw [he]
    exact inv_mem (pow_mem hb 3)
  have ha1 : a^3 = 1 := by
    have hz' : (⟨a^3,pow_mem ha 3⟩ : J) ∈ center J := by
      apply mem_center_iff.mpr
      intro z
      exact Subtype.ext (ha3 z z.property)
    exact congrArg Subtype.val (hz.le hz')
  have hb3 : b^3 = 1 := by simpa only [ha1,one_mul] using hpow
  have hbH : b ∉ H := by
    intro hbH
    exact hxH (hab ▸ H.mul_mem (hJH ha) hbH)
  refine ⟨b,hb,?_,hbH⟩
  exact (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hb3) |>.resolve_left
    (fun h => hbH (orderOf_eq_one_iff.mp h ▸ H.one_mem))

/-- A cubic outside H rules out a cubic in the centralizer of a centerless
normal subgroup J ≤ H, when the ambient cubic rank is at most two. -/
theorem centralizer_intersection_coprime_of_external_cubic
    (J H : Subgroup G) [J.Normal] [H.Normal] (hJH : J ≤ H)
    (hz : center J = ⊥) (hd : 3 ∣ Nat.card J)
    (ho : Nat.Coprime 3 (Nat.card (MulAut.Outer J)))
    (hr : primeRank 3 G ≤ 2) (x : G) (hx : orderOf x = 3) (hxH : x ∉ H) :
    Nat.Coprime 3 (Nat.card (H ⊓ centralizer (J : Set G) : Subgroup G)) := by
  obtain ⟨y,hy,hy3,hyH⟩ := centralizing_cubic_outside J H hJH hz ho x hx hxH
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' 3 hd
  have ha3 : orderOf (a : G) = 3 := (Subgroup.orderOf_coe a).trans ha
  let A := zpowers (a : G)
  let : IsElementaryAbelian 3 A := IsElementaryAbelian.zpowers_of_pow_eq_one
    (ha3 ▸ pow_orderOf_eq_one (a : G))
  have hAJ : A ≤ J := zpowers_le.mpr a.property
  obtain ⟨hE,hcard⟩ := IsElementaryAbelian.fixed_join_card A y hy3
    (A.disjoint_zpowers_of_prime_order_not_mem y hy3 (fun h => hyH (hJH (hAJ h))))
    (fun z hz => mem_centralizer_singleton_iff.mpr (hy z (hAJ hz)))
    (by rw [Nat.card_zpowers,ha3,pow_one] : Nat.card A = 3^1)
  let E := A ⊔ zpowers y
  let C := H ⊓ centralizer (J : Set G)
  let : IsElementaryAbelian 3 E := hE
  have hEC : E ⊓ C = ⊥ := by
    apply le_bot_iff.mp
    rintro z ⟨hzE,hzH,hzC⟩
    have hcomm : zpowers y ≤ centralizer (A : Set G) :=
      zpowers_le.mpr (centralizer_le hAJ hy)
    have hprod : z ∈ (A : Set G) * (zpowers y : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left A (zpowers y)
        (hcomm.trans (Subgroup.centralizer_le_normalizer _))]
      exact hzE
    obtain ⟨a,ha,b,hb,rfl⟩ := hprod
    have hbH : b ∈ H := by
      have := H.mul_mem (H.inv_mem (hJH (hAJ ha))) hzH
      simpa only [inv_mul_cancel_left] using this
    have hb1 : b = 1 :=
      (disjoint_iff.mp (H.disjoint_zpowers_of_prime_order_not_mem y hy3 hyH)).le ⟨hbH,hb⟩
    simp only [hb1,mul_one] at hzC ⊢
    have haZ : (⟨a,hAJ ha⟩ : J) ∈ center J := by
      apply mem_center_iff.mpr
      intro j
      exact Subtype.ext (hzC j j.property)
    exact congrArg Subtype.val (hz.le haZ)
  apply Nat.prime_three.coprime_iff_not_dvd.mpr
  intro hdiv
  exact E.inf_ne_bot_of_elementary_plane C
    (by rw [normalizer_eq_top]; exact le_top) hdiv hcard hr hEC

omit [Finite G] in
private theorem index_coprime_of_centralizer_outer
    (L : Subgroup G) [L.Normal]
    (hC : Nat.Coprime 3 (Nat.card (centralizer (L : Set G))))
    (hO : Nat.Coprime 3 (Nat.card (MulAut.Outer L))) : Nat.Coprime 3 L.index := by
  let f : G →* MulAut.Outer L :=
    (QuotientGroup.mk' (MulAut.innerSubgroup L)).comp MulAut.conjNormal
  have hk : f.ker = L ⊔ centralizer (L : Set G) := by
    change ((QuotientGroup.mk' (MulAut.innerSubgroup L)).comp
      (MulAut.conjNormal : G →* MulAut L)).ker = _
    rw [← MonoidHom.comap_ker,QuotientGroup.ker_mk',MulAut.conjNormal_comap_innerSubgroup]
  have hf : Nat.Coprime 3 f.ker.index := by
    rw [index_ker]
    exact hO.of_dvd_right f.range.card_subgroup_dvd_card
  rw [hk] at hf
  rw [←relIndex_mul_index (show L ≤ L ⊔ centralizer (L : Set G) from le_sup_left)]
  apply Nat.Coprime.mul_right _ hf
  rw [relIndex_sup_left]
  exact hC.of_dvd_right (relIndex_dvd_card _ _)

/-- In the same configuration J has index prime to three inside H. -/
theorem relativeIndex_coprime_of_external_cubic
    (J H : Subgroup G) [J.Normal] [H.Normal] (hJH : J ≤ H)
    (hz : center J = ⊥) (hd : 3 ∣ Nat.card J)
    (ho : Nat.Coprime 3 (Nat.card (MulAut.Outer J)))
    (hr : primeRank 3 G ≤ 2) (x : G) (hx : orderOf x = 3) (hxH : x ∉ H) :
    Nat.Coprime 3 (J.relIndex H) := by
  let B := J.subgroupOf H
  let e : B ≃* J := subgroupOfEquivOfLe hJH
  have hc := centralizer_intersection_coprime_of_external_cubic J H hJH hz hd ho hr x hx hxH
  have hi : (centralizer (B : Set H)).map H.subtype ≤ H ⊓ centralizer (J : Set G) := by
    rintro _ ⟨z,hz,rfl⟩
    refine ⟨z.property,?_⟩
    intro j hj
    exact congrArg Subtype.val (hz ⟨j,hJH hj⟩ hj)
  have hcB : Nat.Coprime 3 (Nat.card (centralizer (B : Set H))) := by
    have hd := card_dvd_of_le hi
    rw [card_map_of_injective H.subtype_injective] at hd
    exact hc.of_dvd_right hd
  have hoB : Nat.Coprime 3 (Nat.card (MulAut.Outer B)) := by
    rwa [Nat.card_congr (MulAut.outerCongr e).toEquiv]
  exact index_coprime_of_centralizer_outer B hcB hoB



private theorem cubic_outside_twoCore_image (H : Subgroup G) [H.Normal]
    (x : G) (hx : orderOf x = 3) (hxH : x ∉ H) :
    QuotientGroup.mk' (pCore 2 G) x ∉ H.map (QuotientGroup.mk' (pCore 2 G)) := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let f := QuotientGroup.mk' H
  intro hmap
  have hs : x ∈ H ⊔ pCore 2 G := by
    have h : x ∈ (H.map q).comap q := hmap
    simpa only [comap_map_eq,q,QuotientGroup.ker_mk'] using h
  have hfH : H.map f = ⊥ := (map_eq_bot_iff H).mpr (QuotientGroup.ker_mk' H).ge
  have hxK : f x ∈ (pCore 2 G).map f := by
    have h := mem_map_of_mem f hs
    simpa only [Subgroup.map_sup,hfH,bot_sup_eq] using h
  have hp : IsPGroup 2 ((pCore 2 G).map f) := pCore_isPGroup.map f
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  have hc : Nat.Coprime 3 (Nat.card ((pCore 2 G).map f)) := by
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have he : orderOf (f x) = 1 := Nat.eq_one_of_dvd_coprimes hc
    (hx ▸ orderOf_map_dvd f x) (Subgroup.orderOf_dvd_natCard _ hxK)
  exact hxH ((QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp he))

/-- The index conclusion lifts from the literal two-core quotient of a
normal C-component, retaining relative index inside H. -/
theorem cComponent_relativeIndex_coprime_of_external_cubic
    (J H : Subgroup G) [J.Normal] [H.Normal] (hJ : J.IsCComponent) (hJH : J ≤ H)
    (hz : center (J ⧸ pCore 2 J) = ⊥) (hd : 3 ∣ Nat.card (J ⧸ pCore 2 J))
    (ho : Nat.Coprime 3 (Nat.card (MulAut.Outer (J ⧸ pCore 2 J))))
    (hr : primeRank 3 G ≤ 2) (x : G) (hx : orderOf x = 3) (hxH : x ∉ H) :
    Nat.Coprime 3 (J.relIndex H) := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let B := J.map q
  let C := H.map q
  let e : (J ⧸ pCore 2 J) ≃* B := cComponentTwoCoreQuotientEquiv hJ
  let : B.Normal := (inferInstance : J.Normal).map q (QuotientGroup.mk'_surjective _)
  let : C.Normal := (inferInstance : H.Normal).map q (QuotientGroup.mk'_surjective _)
  have hzB : center B = ⊥ := by
    apply le_bot_iff.mp
    intro b hb
    have he : e.symm b = 1 := hz.le ((centerCongr e).symm ⟨b,hb⟩).property
    exact e.symm.map_eq_one_iff.mp he
  have hdB : 3 ∣ Nat.card B := by rwa [←Nat.card_congr e.toEquiv]
  have hoB : Nat.Coprime 3 (Nat.card (MulAut.Outer B)) := by
    rwa [←Nat.card_congr (MulAut.outerCongr e).toEquiv]
  have hrQ : primeRank 3 (G ⧸ pCore 2 G) ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 G) pCore_isPGroup).trans hr
  have hqx : orderOf (q x) = 3 := by
    have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
    exact (q.orderOf_map_eq_of_coprime_of_isPGroup_ker hk x (by rw [hx]; decide)).trans hx
  have hi := relativeIndex_coprime_of_external_cubic B C (map_mono hJH)
    hzB hdB hoB hrQ (q x) hqx (cubic_outside_twoCore_image H x hx hxH)
  change Nat.Coprime 3 ((J.map q).relIndex (H.map q)) at hi
  rw [relIndex_map_map,QuotientGroup.ker_mk'] at hi
  have hcore : Nat.Coprime 3 (Nat.card (pCore 2 G)) := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hJcore : Nat.Coprime 3 (J.relIndex (J ⊔ pCore 2 G)) := by
    rw [relIndex_sup_left]
    exact hcore.of_dvd_right (relIndex_dvd_card _ _)
  have hprod := hJcore.mul_right hi
  rw [relIndex_mul_relIndex J (J ⊔ pCore 2 G) (H ⊔ pCore 2 G)
    le_sup_left (sup_le_sup_right hJH _)] at hprod
  exact hprod.of_dvd_right (dvd_of_mul_right_eq _
    (relIndex_mul_relIndex J H (H ⊔ pCore 2 G) hJH le_sup_left))

/-- The original prime-to-three residual is the component, with its actual
inclusion into the normal subgroup H. -/
theorem cComponent_residual_of_external_cubic
    (J H : Subgroup G) [J.Normal] [H.Normal] (hJ : J.IsCComponent) (hJH : J ≤ H)
    [IsSimpleGroup (J ⧸ pCore 2 J)]
    (hz : center (J ⧸ pCore 2 J) = ⊥) (hd : 3 ∣ Nat.card (J ⧸ pCore 2 J))
    (ho : Nat.Coprime 3 (Nat.card (MulAut.Outer (J ⧸ pCore 2 J))))
    (hr : primeRank 3 G ≤ 2) (x : G) (hx : orderOf x = 3) (hxH : x ∉ H) :
    (primeToResidual 3 H).map H.subtype = J := by
  let B := J.subgroupOf H
  let e : B ≃* J := subgroupOfEquivOfLe hJH
  let eQ := QuotientGroup.congr (pCore 2 B) (pCore 2 J) e (pCore_map_iso 2 e)
  let : IsSimpleGroup (B ⧸ pCore 2 B) := eQ.isSimpleGroup
  let := (hJ.subgroupOf hJH).perfect
  have hp : IsPPerfect 2 B := by
    intro N hN hQ
    let := hN
    have hs : Subsingleton (B ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent (B ⧸ N) hQ.isNilpotent
    apply eq_top_iff.mpr
    intro b _
    exact (QuotientGroup.eq_one_iff b).mp (Subsingleton.elim _ _)
  have hgen : primeToResidual 3 B = ⊤ :=
    primeToResidual_eq_top_of_simple_quotient 3 2 (pCore 2 B) pCore_isPGroup hp
      (by rwa [Nat.card_congr eQ.toEquiv])
  have hi := cComponent_relativeIndex_coprime_of_external_cubic J H hJ hJH hz hd ho hr x hx hxH
  have he := primeToResidual_eq_of_subnormal_coprime_index 3 B
    (hJ.subgroupOf hJH).subnormal hgen hi
  rw [he]
  exact map_subgroupOf_eq_of_le hJH

end Theory.GroupTheory
