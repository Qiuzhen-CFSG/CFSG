module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.Index.Intersection
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# Cubic generation and the remaining residual index obstruction

In the equality row Kc = K, every element of Mc killed by cubing acts
trivially on K/O₂(K). Its image modulo the embedded O₂(K) centralizes the
image E₉ of K. An independent cubic element would give three-rank at least
three, contradicting the actual partner's rank bound. Thus every such
element belongs to K. The genuine Xi complement generates K by cubic
elements, so K is characteristic in Mc.

The wreath quotient also shows that every three-element of K is killed
by cubing. Consequently K has index prime to three in Mc exactly when
Mc has no element of order nine. The final applications discharge the
literal partner residual identity and index from that remaining local
condition; they do not assert its ambient proof.

The order-nine exclusion in the equality row and the ambient Held
exclusion remain with `qt-e-152-residual-geometry`. The parent
`qt-e-152-plane-geometry` supplies the earlier source premises in
`ResidualInput` and owns final source assembly.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
15.2.12(4), printed p.1111. These results isolate the additional kernel
control needed after the dihedral normalizer-action calculation.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Chapter1 Chapter1.XiEmbedding Section01 Section03 Section03.InitialSource
open Chapter13.Section08.Components.Swapped.LinearThree

private theorem cubic_mem_of_rank_two
    {A : Type*} [Group A] [Finite A] (K : Subgroup A) [K.Normal]
    [IsElementaryAbelian 3 (K ⧸ pCore 2 K)]
    (hcard : Nat.card (K ⧸ pCore 2 K) = 3 ^ 2)
    (hA : primeRank 3 A ≤ 2) (x : A) (hx : x ^ 3 = 1)
    (hc : ∀ y ∈ K, ⁅x,y⁆ ∈ K.pCoreIn 2) : x ∈ K := by
  let Q := K.pCoreIn 2
  let : Q.Normal := inferInstanceAs (((pCore 2 K).map K.subtype).Normal)
  let q := QuotientGroup.mk' Q
  let f := q.comp K.subtype
  have hk : f.ker = pCore 2 K := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact comap_map_eq_self_of_injective K.subtype_injective _
  let e : (K ⧸ pCore 2 K) ≃* K.map q :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      ((QuotientGroup.quotientKerEquivRange f).trans
        (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, range_subtype])))
  let : IsElementaryAbelian 3 (K.map q) :=
    IsElementaryAbelian.of_injective e.symm.toMonoidHom e.symm.injective
  have hm : q x ∈ K.map q := by
    by_contra hn
    have hn1 : q x ≠ 1 := fun he => hn (he ▸ (K.map q).one_mem)
    have hxp : orderOf (q x) = 3 :=
      orderOf_eq_prime (by rw [← map_pow,hx,map_one]) hn1
    have hf : K.map q ≤ centralizer ({q x} : Set (A ⧸ Q)) := by
      rintro _ ⟨y,hy,rfl⟩
      apply mem_centralizer_singleton_iff.mpr
      apply Eq.symm
      apply commutatorElement_eq_one_iff_mul_comm.mp
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr (hc y hy)
    have hr := IsElementaryAbelian.primeRank_ge_of_fixed_join (K.map q) (q x)
      hxp hn hf ((Nat.card_congr e.symm.toEquiv).trans hcard)
    have hb := (primeRank_quotient_le_of_isTwoGroup 3 (by decide) Q
      (isPGroup_pCoreIn 2 K)).trans hA
    omega
  have hh : x ∈ (K.map q).comap q := hm
  rwa [comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr (pCoreIn_le 2 K)] at hh

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B : Subgroup G}

omit [Finite G] in
private theorem quotient_action_kernel_commutator
    (he : partnerSpan H Mc = residual H) (hKM : residual H ≤ Mc)
    {x : Mc} (hx : x ∈ (partnerQuotientAction H Mc he).ker)
    {y : Mc} (hy : y ∈ (residual H).subgroupOf Mc) :
    ⁅x,y⁆ ∈ ((residual H).subgroupOf Mc).pCoreIn 2 := by
  let K := (residual H).subgroupOf Mc
  let yK : residual H := ⟨(y : G),hy⟩
  let n := inclusion (partner_normalizes_of_eq H Mc he) x
  let y' := (residual H).normalizerMonoidHom n yK
  have hf : QuotientGroup.mk' (pCore 2 (residual H)) y' =
      QuotientGroup.mk' (pCore 2 (residual H)) yK := by
    have hh := DFunLike.congr_fun (show partnerQuotientAction H Mc he x = 1 from hx)
      (QuotientGroup.mk' (pCore 2 (residual H)) yK)
    change quotientAut (pCore 2 (residual H))
      ((residual H).normalizerMonoidHom n) (QuotientGroup.mk' _ yK) = _ at hh
    simpa only [quotientAut_apply_mk, MulAut.one_apply] using hh
  have hz : y' * yK⁻¹ ∈ pCore 2 (residual H) := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (pCore 2 (residual H)) (y' * yK⁻¹) = 1
    rw [map_mul,map_inv,hf,mul_inv_cancel]
  have hzG : (⁅x,y⁆ : Mc).val ∈ (residual H).pCoreIn 2 := ⟨y' * yK⁻¹,hz,rfl⟩
  have hecore : (K.pCoreIn 2).map Mc.subtype = (residual H).pCoreIn 2 := by
    rw [map_pCoreIn_of_injective 2 K Mc.subtype Mc.subtype_injective,
      map_subgroupOf_eq_of_le hKM]
  rw [← hecore] at hzG
  obtain ⟨z,hz,hzx⟩ := hzG
  exact (show z = ⁅x,y⁆ from Subtype.ext hzx) ▸ hz

/-- In the equality row, every element killed by cubing belongs to K. -/
theorem ResidualInput.cubic_mem_residual_of_eq {h : ChosenSmallSource T M Mc V}
    (d : ResidualInput h H B) (he : partnerSpan H Mc = residual H)
    (x : Mc) (hx : x ^ 3 = 1) : (x : G) ∈ residual H := by
  have hHM : H ≤ Mc :=
    (source_centralizing_HStar_le_seed_centralizer h.ambient T h.maximal
      d.outside h.centralizing).trans (centralizer_le_partner T h.partner)
  have hKM : residual H ≤ Mc := (map_subtype_le _).trans hHM
  let K := (residual H).subgroupOf Mc
  let e : K ≃* residual H := subgroupOfEquivOfLe hKM
  let eQ := QuotientGroup.congr (pCore 2 K) (pCore 2 (residual H)) e (pCore_map_iso 2 e)
  let a := eQ.trans (residualQuotientEquiv H d.quotient.some)
  let : IsElementaryAbelian 3 (K ⧸ pCore 2 K) :=
    IsElementaryAbelian.of_injective a.toMonoidHom a.injective
  have hcard : Nat.card (K ⧸ pCore 2 K) = 3 ^ 2 :=
    (Nat.card_congr a.toEquiv).trans WreathModel.cubicBase_card
  let : K.Normal := normal_subgroupOf_of_le_normalizer (partner_normalizes_of_eq H Mc he)
  have hk : x ∈ (partnerQuotientAction H Mc he).ker :=
    d.threeResidual_le_action_kernel_of_eq he
      (mem_primeToResidual_of_pow (p := 3) (n := 1) hx)
  exact cubic_mem_of_rank_two K hcard
    ((h.ambient.twoLocal_sqtk (partner_mem_overgroups h).1.1).stronglyQuasithin
      3 Nat.prime_three (by decide)) x hx
    (fun y hy => quotient_action_kernel_commutator he hKM hk hy)

/-- The residual is generated by the partner's elements killed by cubing.
This does not yet assert that all elements of three-power order are cubic. -/
theorem ResidualInput.cubic_generation_of_eq {h : ChosenSmallSource T M Mc V}
    (d : ResidualInput h H B) (he : partnerSpan H Mc = residual H) :
    closure {x : Mc | x ^ 3 = 1} = (residual H).subgroupOf Mc := by
  let C := closure {x : Mc | x ^ 3 = 1}
  apply le_antisymm
  · rw [closure_le]
    exact fun x hx => d.cubic_mem_residual_of_eq he x hx
  · obtain ⟨P,hP⟩ := d.localInput
    let a := hP.complementQuotientEquiv.trans (residualQuotientEquiv H d.quotient.some)
    let : IsElementaryAbelian 3 P :=
      IsElementaryAbelian.of_injective a.toMonoidHom a.injective
    have hKM : residual H ≤ Mc := le_sup_left.trans hP.overgroup
    have hPK : P ≤ residual H := le_sup_right.trans hP.complement.le
    have hKC : residual H ≤ C.map Mc.subtype := by
      rw [← hP.generation, closure_le]
      rintro _ ⟨n,hn,b,hb,rfl⟩
      have hg : n * b * n⁻¹ ∈ Mc := Mc.mul_mem
        (Mc.mul_mem (hKM (pCoreIn_le 2 (residual H) hn)) (hKM (hPK hb)))
        (Mc.inv_mem (hKM (pCoreIn_le 2 (residual H) hn)))
      have hp : (n * b * n⁻¹) ^ 3 = 1 := by
        rw [conj_pow, elemPow_eq_one_of_isElementaryAbelian (p := 3) b hb,
          mul_one, mul_inv_cancel]
      exact ⟨⟨n * b * n⁻¹,hg⟩,subset_closure (show (⟨n * b * n⁻¹,hg⟩ : Mc) ^ 3 = 1
        from Subtype.ext hp),rfl⟩
    intro x hx
    obtain ⟨y,hy,hyx⟩ := hKC hx
    exact (show y = x from Subtype.ext hyx) ▸ hy

/-- In the equality row, K is characteristic in the literal partner. -/
theorem ResidualInput.residual_characteristic_of_eq {h : ChosenSmallSource T M Mc V}
    (d : ResidualInput h H B) (he : partnerSpan H Mc = residual H) :
    ((residual H).subgroupOf Mc).Characteristic := by
  rw [← d.cubic_generation_of_eq he]
  apply characteristic_iff_map_le.mpr
  intro e
  rw [MonoidHom.map_closure, closure_le]
  rintro _ ⟨x,hx,rfl⟩
  apply Subgroup.subset_closure
  change (e x) ^ 3 = 1
  rw [← map_pow, show x ^ 3 = 1 from hx, map_one]

private theorem cubic_of_three_power_over_two_core
    {A : Type*} [Group A] [IsElementaryAbelian 3 (A ⧸ pCore 2 A)]
    (x : A) {n : ℕ} (hx : x ^ (3 ^ n) = 1) : x ^ 3 = 1 := by
  have hm : x ^ 3 ∈ pCore 2 A := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (pCore 2 A) (x ^ 3) = 1
    rw [map_pow]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 3 (A ⧸ pCore 2 A)) _
  let y : pCore 2 A := ⟨x ^ 3,hm⟩
  obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := A)) y
  have hy : y ^ (3 ^ n) = 1 := by
    apply Subtype.ext
    change (x ^ 3) ^ (3 ^ n) = 1
    rw [← pow_mul, Nat.mul_comm 3, pow_mul, hx, one_pow]
  have ho : orderOf y = 1 := Nat.eq_one_of_dvd_coprimes
    ((by decide : Nat.Coprime 2 3).pow k n)
    (orderOf_dvd_of_pow_eq_one hk) (orderOf_dvd_of_pow_eq_one hy)
  exact congrArg Subtype.val (orderOf_eq_one_iff.mp ho)

/-- All three-elements of the actual residual have exponent dividing three. -/
theorem ResidualInput.residual_three_power_cubic {h : ChosenSmallSource T M Mc V}
    (d : ResidualInput h H B) (x : residual H) {n : ℕ}
    (hx : x ^ (3 ^ n) = 1) : x ^ 3 = 1 := by
  let e := residualQuotientEquiv H d.quotient.some
  let : IsElementaryAbelian 3 ((residual H) ⧸ pCore 2 (residual H)) :=
    IsElementaryAbelian.of_injective e.toMonoidHom e.injective
  exact cubic_of_three_power_over_two_core x hx

/-- In particular K has no element of order nine. -/
theorem ResidualInput.residual_order_ne_nine {h : ChosenSmallSource T M Mc V}
    (d : ResidualInput h H B) (x : residual H) : orderOf x ≠ 9 := by
  intro hx
  have hp := d.residual_three_power_cubic x (n := 2)
    (show x ^ (3 ^ 2) = 1 by rw [show 3 ^ 2 = 9 by decide, ← hx, pow_orderOf_eq_one])
  have hd := orderOf_dvd_of_pow_eq_one hp
  rw [hx] at hd
  exact (by decide : ¬ 9 ∣ 3) hd

private theorem cubic_of_three_power_of_no_nine
    {A : Type*} [Group A] (h9 : ∀ x : A, orderOf x ≠ 9)
    (x : A) {n : ℕ} (hx : x ^ (3 ^ n) = 1) : x ^ 3 = 1 := by
  obtain ⟨k,_,hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
    (orderOf_dvd_of_pow_eq_one hx)
  have hk1 : k ≤ 1 := by
    by_contra hn
    have hd : 9 ∣ orderOf x := by
      rw [hk]
      exact (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < 3)).mpr (by omega : 2 ≤ k)
    exact h9 (x ^ (orderOf x / 9))
      (orderOf_pow_orderOf_div (by rw [hk]; exact pow_ne_zero _ (by decide)) hd)
  apply orderOf_dvd_iff_pow_eq_one.mp
  rw [hk]
  exact (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < 3)).mpr hk1

/-- The remaining equality-row index condition is exactly exclusion of
order nine in the actual partner, rather than a rank-only inference. -/
theorem ResidualInput.index_coprime_iff_no_order_nine_of_eq
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B)
    (he : partnerSpan H Mc = residual H) :
    Nat.Coprime 3 ((partnerSpan H Mc).subgroupOf Mc).index ↔
      ∀ x : Mc, orderOf x ≠ 9 := by
  constructor
  · intro hi x hx
    have hR := d.residual_equality_of_index hi
    have hxR : (x : G) ∈ threePrimeResidual Mc := by
      rw [threePrimeResidual_eq]
      exact mem_map_of_mem Mc.subtype (mem_primeToResidual_of_pow (p := 3) (n := 2)
        (show x ^ (3 ^ 2) = 1 by rw [show 3 ^ 2 = 9 by decide, ← hx, pow_orderOf_eq_one]))
    have hxK : (x : G) ∈ residual H := by rwa [← hR, he] at hxR
    let y : residual H := ⟨x,hxK⟩
    apply d.residual_order_ne_nine y
    have hy : orderOf y = orderOf x :=
      (orderOf_injective (residual H).subtype (residual H).subtype_injective y).symm.trans
        (orderOf_injective Mc.subtype Mc.subtype_injective x)
    exact hy.trans hx
  · intro h9
    let S : Sylow 3 Mc := Classical.choice inferInstance
    have hSK : (S : Subgroup Mc) ≤ (residual H).subgroupOf Mc := by
      intro x hx
      obtain ⟨n,hn⟩ := S.isPGroup' ⟨x,hx⟩
      exact d.cubic_mem_residual_of_eq he x
        (cubic_of_three_power_of_no_nine h9 x (congrArg Subtype.val hn))
    rw [he]
    exact (Nat.prime_three.coprime_iff_not_dvd.mpr S.not_dvd_index).coprime_dvd_right
      (index_dvd_of_le hSK)

/-- The local order-nine exclusion discharges the literal residual identity.
Its proof from the ambient chosen-module hypotheses stays with this owner. -/
theorem ResidualInput.residual_equality_of_no_order_nine
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B)
    (h9 : partnerSpan H Mc = residual H → ∀ x : Mc, orderOf x ≠ 9) :
    partnerSpan H Mc = threePrimeResidual Mc := by
  by_cases he : partnerSpan H Mc = residual H
  · exact d.residual_equality_of_index
      ((d.index_coprime_iff_no_order_nine_of_eq he).mpr (h9 he))
  · exact d.residual_equality_of_ne he

/-- The resulting prime-to-three index on the original partner span. -/
theorem ResidualInput.index_coprime_of_no_order_nine
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B)
    (h9 : partnerSpan H Mc = residual H → ∀ x : Mc, orderOf x ≠ 9) :
    Nat.Coprime 3 ((partnerSpan H Mc).subgroupOf Mc).index := by
  by_cases he : partnerSpan H Mc = residual H
  · exact (d.index_coprime_iff_no_order_nine_of_eq he).mpr (h9 he)
  · exact d.index_coprime_of_ne he

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
