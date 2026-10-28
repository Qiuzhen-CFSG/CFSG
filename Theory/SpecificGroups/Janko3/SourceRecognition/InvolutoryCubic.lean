module
public import Theory.SpecificGroups.Alternating.FiveInvolutionFusion
public import Mathlib.GroupTheory.Sylow

/-!
# Involutory cubic inversion from an alternating quotient

An involution with nontrivial image in A₅ has a conjugate whose product
with it has cubic image. The element of order three in the cyclic group
of that product is inverted by the original involution. When the whole
group has order 1920, Sylow conjugacy carries the inverter to every
specified cubic. No complement to the kernel is assumed.

This supplies the involutory inverter in Baumeister, *A geometry for
groups of J₃-type* (2007), Lemma 2.4, p.495, from the weaker retained
H-type hypotheses, once an outside-core involution is constructed.
-/

public noncomputable section
open Subgroup
namespace Sporadic.Janko3.SourceRecognition.InvolutoryCubic
private def a : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 3 4, by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
private def b : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 1 2 * Equiv.swap 3 4, by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
private theorem a_order : orderOf a = 2 :=
  orderOf_eq_prime (by decide +kernel) (by decide +kernel)
private theorem b_order : orderOf b = 2 :=
  orderOf_eq_prime (by decide +kernel) (by decide +kernel)
private theorem ab_order : orderOf (a * b) = 3 :=
  orderOf_eq_prime (by decide +kernel) (by decide +kernel)

theorem cubic_inverted_by_involution {H : Type*} [Group H] [Finite H]
    (q : H →* alternatingGroup (Fin 5)) (hq : Function.Surjective q)
    (t : H) (ht : orderOf t = 2) (hqt : q t ≠ 1) :
    ∃ v : H, orderOf v = 3 ∧ t * v * t⁻¹ = v⁻¹ := by
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  have htq : orderOf (q t) = 2 := orderOf_eq_prime
    (by rw [← map_pow, ht2, map_one]) hqt
  obtain ⟨k,hk⟩ := isConj_iff.mp
    (alternatingGroup.five_involutions_isConj a (q t) a_order htq)
  let c := MulAut.conj k b
  have hc : orderOf c = 2 := ((MulAut.conj k).orderOf_eq b).trans b_order
  have htc : orderOf (q t * c) = 3 := by
    rw [← hk]
    change orderOf (MulAut.conj k a * MulAut.conj k b) = 3
    rw [← map_mul, (MulAut.conj k).orderOf_eq, ab_order]
  obtain ⟨gbar,hgbar⟩ := isConj_iff.mp
    (alternatingGroup.five_involutions_isConj (q t) c htq hc)
  obtain ⟨g,rfl⟩ := hq gbar
  let u := g * t * g⁻¹
  let x := t * u
  have hu2 : u ^ 2 = 1 := by
    change (MulAut.conj g t) ^ 2 = 1
    rw [← map_pow, ht2, map_one]
  have hqx : orderOf (q x) = 3 := by
    dsimp only [x,u]
    rw [map_mul, map_mul, map_mul, map_inv, hgbar]
    exact htc
  have hd : 3 ∣ orderOf x := hqx ▸ orderOf_map_dvd q x
  have hinv : t * x * t⁻¹ = x⁻¹ := by
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using ht2)
    have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hu2)
    dsimp only [x]
    rw [mul_inv_rev, htinv, huinv]
    calc
      t * (t * u) * t = (t * t) * u * t := by group
      _ = u * t := by rw [← pow_two, ht2, one_mul]
  refine ⟨x ^ (orderOf x / 3), orderOf_pow_orderOf_div (orderOf_pos x).ne' hd, ?_⟩
  have hh := congrArg (fun y : H => y ^ (orderOf x / 3)) hinv
  simpa only [conj_pow, inv_pow] using hh

theorem inverter_of_alternating_quotient {H : Type*} [Group H] [Finite H]
    (hH : Nat.card H = 1920)
    (q : H →* alternatingGroup (Fin 5)) (hq : Function.Surjective q)
    (t : H) (ht : orderOf t = 2) (hqt : q t ≠ 1)
    (s : H) (hs : orderOf s = 3) :
    ∃ r : H, orderOf r = 2 ∧ r * s * r⁻¹ = s⁻¹ := by
  obtain ⟨v,hv,htv⟩ := cubic_inverted_by_involution q hq t ht hqt
  have hcard (x : H) (hx : orderOf x = 3) :
      Nat.card (zpowers x) = 3 ^ (Nat.card H).factorization 3 := by
    rw [Nat.card_zpowers,hx,hH]
    decide +kernel
  let V : Sylow 3 H := Sylow.ofCard (zpowers v) (hcard v hv)
  let S : Sylow 3 H := Sylow.ofCard (zpowers s) (hcard s hs)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq H V S
  have hmap : (zpowers v).map (MulAut.conj g).toMonoidHom = zpowers s :=
    congrArg (fun P : Sylow 3 H => (P : Subgroup H)) hg
  let a := MulAut.conj g
  have hmem : a.symm s ∈ zpowers v := by
    have hh : s ∈ (zpowers v).map a.toMonoidHom := hmap.symm ▸ mem_zpowers s
    exact mem_map_equiv.mp hh
  obtain ⟨n,hn⟩ := mem_zpowers_iff.mp hmem
  have hinv : t * a.symm s * t⁻¹ = (a.symm s)⁻¹ := by
    rw [← hn]
    have hh := congrArg (fun y : H => y ^ n) htv
    simpa only [conj_zpow, inv_zpow] using hh
  refine ⟨a t,(a.orderOf_eq t).trans ht,?_⟩
  have hh := congrArg a hinv
  simpa only [map_mul,map_inv,a.apply_symm_apply] using hh

end Sporadic.Janko3.SourceRecognition.InvolutoryCubic
