module
public import Theory.GroupTheory.Recognition.QuasithinM23.CentralInvolution
public import Theory.GroupTheory.ElementaryQuotientCocycles
public import Theory.Representation.AlternatingSevenConjugatePair.Model.InnerElements
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Involution fusion outside an exceptional elementary core

In a faithful binary four-dimensional A₇ action every involution fixes a
plane. Its fixed subgroup therefore has order four, and the elementary
coboundary lemma shows that two involution lifts with the same nontrivial
quotient image are conjugate by the original core. Since the involutions
of A₇ form one class, all involutions outside the core form one class in
any such extension. No splitting of the extension is assumed.

This is the local fusion calculation used in Aschbacher–Smith 5.2.13,
printed p.654 (`refs/quasithin.pdf`). The ambient source consumer joins this
class to the core class using the original left natural block.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace Theory.GroupTheory.QuasithinM23

private theorem seven_involution_cycleType (x : alternatingGroup (Fin 7))
    (hx : orderOf x = 2) : x.val.cycleType = {2,2} := by
  have ho : orderOf x.val = 2 := (Subgroup.orderOf_coe x).trans hx
  obtain ⟨k,hk⟩ := Equiv.Perm.cycleType_prime_order (ho ▸ Nat.prime_two)
  rw [ho] at hk
  have hb := x.val.sum_cycleType_le
  rw [hk] at hb
  simp only [Multiset.sum_replicate,nsmul_eq_mul,Nat.cast_id,Fintype.card_fin] at hb
  have hs := Equiv.Perm.mem_alternatingGroup.mp x.property
  rw [Equiv.Perm.sign_of_cycleType',hk] at hs
  have hk2 : k ≤ 2 := by omega
  have hk1 : k = 1 := by
    interval_cases k
    · norm_num at hs
    · rfl
    · norm_num at hs
  simpa [hk1] using hk

private theorem seven_involutions_isConj (x y : alternatingGroup (Fin 7))
    (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y := by
  apply alternatingGroup.isConj_of (Equiv.Perm.isConj_iff_cycleType_eq.mpr
    ((seven_involution_cycleType x hx).trans (seven_involution_cycleType y hy).symm))
  rw [←Equiv.Perm.sum_cycleType,seven_involution_cycleType x hx]
  decide

variable {G : Type*} [Group G] [Finite G]
  (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
  (hU : Nat.card U = 16)
  (q : G →* alternatingGroup (Fin 7)) (hq : Function.Surjective q)
  (hk : q.ker = U) (hC : centralizer (U : Set G) = U)

include hU q hq hk hC

private theorem fixed_card (t : G) (ht : orderOf (q t) = 2) :
    Nat.card ((MulAut.conjNormal t : MulAut U).toMonoidHom.eqLocus (MonoidHom.id U)) = 4 := by
  let ρ := NormalElementaryQuotient.representation U q hq (hk.trans hC.symm)
  have hf := NormalElementaryQuotient.representation_injective U q hq (hk.trans hC.symm)
  have hd : Module.finrank (ZMod 2) (Additive U) = 4 := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    calc
      2 ^ Module.finrank (ZMod 2) (Additive U) = Nat.card (Additive U) := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
      _ = 2^4 := (Nat.card_congr Additive.toMul).trans hU
  have hc := AlternatingSevenConjugatePair.Model.involution_fixedCodim ρ hf hd (q t) ht
  have hsum := BinaryOffender.fixedCodim_add_finrank ρ (zpowers (q t))
  have hdim : Module.finrank (ZMod 2) (BinaryOffender.fixedSpace ρ (zpowers (q t))) = 2 := by omega
  let e : ((MulAut.conjNormal t : MulAut U).toMonoidHom.eqLocus (MonoidHom.id U)) ≃
      BinaryOffender.fixedSpace ρ (zpowers (q t)) := {
    toFun u := ⟨Additive.ofMul u.val, by
      rw [BinaryOffender.mem_fixedSpace_zpowers_iff]
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [NormalElementaryQuotient.representation_apply]
      exact congrArg Subtype.val u.property⟩
    invFun v := ⟨v.val.toMul, by
      have hv := (BinaryOffender.mem_fixedSpace_zpowers_iff ρ (q t) v.val).mp v.property
      apply Subtype.ext
      exact (NormalElementaryQuotient.representation_apply U q hq (hk.trans hC.symm) t v.val).symm.trans
        (congrArg (fun w : Additive U => (w.toMul : G)) hv)⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  rw [Nat.card_congr e,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hdim]
  norm_num

/-- Involutions with the same nontrivial quotient image are conjugate by the
original elementary core, without a splitting hypothesis. -/
theorem involution_lifts_conjugate {s t : G} (hs : orderOf s = 2) (ht : orderOf t = 2)
    (he : q s = q t) (hne : q t ≠ 1) : ∃ u : U, (u : G)*t*(u : G)⁻¹ = s := by
  have hs2 : s*s = 1 := by simpa only [hs,pow_two] using pow_orderOf_eq_one s
  have ht2 : t*t = 1 := by simpa only [ht,pow_two] using pow_orderOf_eq_one t
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_left hs2
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_left ht2
  have hqt : orderOf (q t) = 2 := orderOf_eq_prime
    (by rw [←map_pow]; simpa only [ht,map_one] using congrArg q (pow_orderOf_eq_one t)) hne
  let α : U →* U := (MulAut.conjNormal t : MulAut U).toMonoidHom
  have ha (u : U) : α (α u) = u := by
    apply Subtype.ext
    change t*(t*(u : G)*t⁻¹)*t⁻¹ = u
    rw [hti]
    calc _ = (t*t)*(u : G)*(t*t) := by group
         _ = _ := by rw [ht2]; group
  have hc : Nat.card (α.eqLocus (MonoidHom.id U)) ^ 2 = Nat.card U := by
    rw [fixed_card U hU q hq hk hC t hqt,hU]
    norm_num
  have hu : s*t⁻¹ ∈ U := by
    rw [←hk,MonoidHom.mem_ker,map_mul,map_inv,he,mul_inv_cancel]
  let u : U := ⟨s*t⁻¹,hu⟩
  have hui : (s*t⁻¹)⁻¹ = s*t⁻¹ := by
    have hh := elemPow_eq_one_of_isElementaryAbelian (p := 2) _ hu
    exact inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hh)
  have hfix : α u = u := by
    apply Subtype.ext
    change t*(s*t⁻¹)*t⁻¹ = s*t⁻¹
    calc
      t*(s*t⁻¹)*t⁻¹ = t*s := by rw [hti]; simp only [mul_assoc,ht2,mul_one]
      _ = (s*t⁻¹)⁻¹ := by rw [mul_inv_rev,inv_inv,hsi]
      _ = s*t⁻¹ := hui
  obtain ⟨v,hv⟩ := elementary_fixed_is_coboundary α ha hc u hfix
  refine ⟨v,?_⟩
  have hvG := congrArg (fun w : U => (w : G)) hv
  change s*t⁻¹ = (v : G)*(t*(v : G)⁻¹*t⁻¹) at hvG
  have hh := congrArg (fun w : G => w*t) hvG
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh.symm

/-- All involutions outside the elementary core form one class in the
exceptional extension itself. -/
theorem noncore_involutions_isConj {s t : G}
    (hs : orderOf s = 2) (ht : orderOf t = 2) (hsU : s ∉ U) (htU : t ∉ U) : IsConj s t := by
  have hs1 : q s ≠ 1 := fun he => hsU (hk ▸ (show s ∈ q.ker from he))
  have ht1 : q t ≠ 1 := fun he => htU (hk ▸ (show t ∈ q.ker from he))
  have hqs : orderOf (q s) = 2 := orderOf_eq_prime
    (by rw [←map_pow]; simpa only [hs,map_one] using congrArg q (pow_orderOf_eq_one s)) hs1
  have hqt : orderOf (q t) = 2 := orderOf_eq_prime
    (by rw [←map_pow]; simpa only [ht,map_one] using congrArg q (pow_orderOf_eq_one t)) ht1
  obtain ⟨a,ha⟩ := (isConj_iff.mp (seven_involutions_isConj (q s) (q t) hqs hqt))
  obtain ⟨g,rfl⟩ := hq a
  let s' := g*s*g⁻¹
  have he : q s' = q t := by simpa only [s',map_mul,map_inv] using ha
  have hs' : orderOf s' = 2 := ((MulAut.conj g).orderOf_eq s).trans hs
  obtain ⟨u,hu⟩ := involution_lifts_conjugate U hU q hq hk hC ht hs' he.symm (he ▸ ht1)
  apply isConj_iff.mpr
  refine ⟨(u : G)*g,?_⟩
  calc _ = (u : G)*(g*s*g⁻¹)*(u : G)⁻¹ := by group
       _ = t := hu

end Theory.GroupTheory.QuasithinM23
