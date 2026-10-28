module
public import Theory.GroupTheory.SylowNormalizerOvergroup
public import Theory.GroupTheory.RelativeComplementProjection
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

/-!
# Normalizing a complement by its unique inverting involution

Let K be normal in an ambient group, with K = XB and X of odd
order. Suppose K/X and B are isomorphic to a group with a unique involution,
and the involution of B inverts X. Every subgroup A disjoint from X and
containing a Sylow subgroup that normalizes B normalizes B itself.

The unique involution of B belongs to that Sylow. Every involution of K
has the same nontrivial quotient image, so disjointness makes A fix it.
Its centralizer in K is exactly B, by inversion and the odd order of X.

Source application: Aschbacher--Smith, 12.5.4, printed p.819, for the
E₄₉-by-SL₂(7) point component. The proof is independent of that geometry.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G Q : Type*} [Group G] [Group Q]

/-- An odd-kernel quotient with a unique involution determines its inverting
complement inside every disjoint overgroup of the original Sylow. -/
theorem normalizes_complement_of_unique_quotient_involution
    (K X B A : Subgroup G) [K.Normal]
    (hXK : X ≤ K) (hBK : B ≤ K) (hgen : X ⊔ B = K)
    (hXA : Disjoint X A)
    (hX : Odd (Nat.card X))
    (q : K →* Q) (hq : q.ker = X.subgroupOf K)
    (e : B ≃* Q)
    (huniq : ∃! z : Q, orderOf z = 2)
    (hinv : ∀ z : B, orderOf z = 2 → ∀ x ∈ X, (z : G) * x * (z : G)⁻¹ = x⁻¹)
    (R : Sylow 2 G) (hRB : (R : Subgroup G) ≤ normalizer (B : Set G))
    (hRA : (R : Subgroup G) ≤ A) : A ≤ normalizer (B : Set G) := by
  obtain ⟨u,hu,huuniq⟩ := huniq
  let z : B := e.symm u
  have hz : orderOf z = 2 := (e.symm.orderOf_eq u).trans hu
  have hzg : orderOf (z : G) = 2 := (orderOf_coe z).trans hz
  have uniqueB (b : B) (hb : orderOf b = 2) : b = z := by
    apply e.injective
    exact (huuniq (e b) ((e.orderOf_eq b).trans hb)).trans (e.apply_symm_apply u).symm
  have hRz : (R : Subgroup G) ≤ normalizer (zpowers (z : G) : Set G) := by
    apply le_normalizer_iff.mpr
    intro r hr a ha
    have hzB := (mem_normalizer_iff.mp (hRB hr) (z : G)).mp z.property
    have hzfix : r * (z : G) * r⁻¹ = z := by
      apply congrArg Subtype.val (uniqueB ⟨_,hzB⟩ ?_)
      exact (orderOf_coe (⟨_,hzB⟩ : B)).symm.trans
        (((MulAut.conj r).orderOf_eq (z : G)).trans hzg)
    have hh : (zpowers (z : G)).map (MulAut.conj r).toMonoidHom = zpowers (z : G) := by
      rw [MonoidHom.map_zpowers]
      exact congrArg zpowers hzfix
    exact hh ▸ mem_map_of_mem (MulAut.conj r).toMonoidHom ha
  have hzR : (z : G) ∈ R := by
    have hp : IsPGroup 2 (zpowers (z : G)) := IsPGroup.of_card (n := 1) (by
      simp only [Nat.card_zpowers,hzg,pow_one])
    exact hp.le_sylow_of_normalized R hRz (mem_zpowers _)
  have hzA : (z : G) ∈ A := hRA hzR
  have hx2 (x : G) (hx : x ∈ X) (hh : x ^ 2 = 1) : x = 1 := by
    have hd := orderOf_dvd_of_pow_eq_one hh
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · exact orderOf_eq_one_iff.mp h1
    · have ho := hX.of_dvd_nat (orderOf_dvd_natCard X hx)
      rw [h2] at ho
      exact (by decide : ¬ Odd 2) ho |>.elim
  have image (t : K) (ht : orderOf t = 2) : q t = u := by
    apply huuniq
    have hd : orderOf (q t) ∣ 2 := ht ▸ orderOf_map_dvd q t
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · have htX : (t : G) ∈ X := by
        have hk : t ∈ q.ker := orderOf_eq_one_iff.mp h1
        rw [hq] at hk
        exact hk
      have ht1 : t = 1 := Subtype.ext (hx2 t htX (by
        have hh := congrArg (fun k : K => (k : G)) (pow_orderOf_eq_one t)
        simpa only [ht,Subgroup.coe_pow,Subgroup.coe_one] using hh))
      simp [ht1] at ht
    · exact h2
  have hzK : (z : G) ∈ K := hBK z.property
  have fixes (a : G) (ha : a ∈ A) : a * (z : G) * a⁻¹ = z := by
    have hz'K : a * (z : G) * a⁻¹ ∈ K :=
      (inferInstance : K.Normal).conj_mem _ hzK a
    have hz' : orderOf (⟨_,hz'K⟩ : K) = 2 :=
      (orderOf_coe (⟨_,hz'K⟩ : K)).symm.trans
        (((MulAut.conj a).orderOf_eq (z : G)).trans hzg)
    have hz0 : orderOf (⟨z,hzK⟩ : K) = 2 :=
      (orderOf_coe (⟨z,hzK⟩ : K)).symm.trans hzg
    have hk : (⟨_,hz'K⟩ : K) * (⟨z,hzK⟩ : K)⁻¹ ∈ q.ker := by
      change q (_ * _) = 1
      rw [map_mul,map_inv,image _ hz',image _ hz0,mul_inv_cancel]
    rw [hq] at hk
    have hx : a * (z : G) * a⁻¹ * (z : G)⁻¹ ∈ X := hk
    have heq : a * (z : G) * a⁻¹ * (z : G)⁻¹ = 1 :=
      disjoint_def.mp hXA hx
        (A.mul_mem (A.mul_mem (A.mul_mem ha hzA) (A.inv_mem ha)) (A.inv_mem hzA))
    exact mul_inv_eq_one.mp heq
  have hXN : (X.subgroupOf K).Normal := hq ▸ (inferInstance : q.ker.Normal)
  have hNK : K ≤ normalizer (X : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hXK).mp hXN
  have central (k : G) (hk : k ∈ K) (hc : k * z = z * k) : k ∈ B := by
    have hprod : (↑(X ⊔ B) : Set G) = (X : Set G) * (B : Set G) :=
      coe_mul_of_right_le_normalizer_left X B (hBK.trans hNK)
    have hk' : k ∈ (X : Set G) * (B : Set G) := by rw [←hprod,hgen]; exact hk
    obtain ⟨x,hx,b,hb,rfl⟩ := hk'
    have hzb : b * (z : G) * b⁻¹ = z := by
      have hh := uniqueB ((MulAut.conj (⟨b,hb⟩ : B)) z)
        (((MulAut.conj (⟨b,hb⟩ : B)).orderOf_eq z).trans hz)
      exact congrArg Subtype.val hh
    have hbc : b * (z : G) = z * b := mul_inv_eq_iff_eq_mul.mp hzb
    have hxc : x * (z : G) = z * x := by
      apply mul_right_cancel (b := b)
      calc
        x * (z : G) * b = (x * b) * z := by rw [mul_assoc,←hbc,←mul_assoc]
        _ = z * (x * b) := hc
        _ = _ := (mul_assoc _ _ _).symm
    have hxx : x = x⁻¹ := by
      calc
        x = (z : G) * x * (z : G)⁻¹ := by rw [←hxc,mul_inv_cancel_right]
        _ = x⁻¹ := hinv z hz x hx
    have hx1 : x = 1 := hx2 x hx (by
      calc
        x ^ 2 = x * x := pow_two x
        _ = x * x⁻¹ := congrArg (x * ·) hxx
        _ = 1 := mul_inv_cancel x)
    change x * b ∈ B
    rw [hx1,one_mul]
    exact hb
  apply le_normalizer_iff.mpr
  intro a ha b hb
  have hzfix := fixes a ha
  have hbc : b * (z : G) = z * b := by
    have hh := uniqueB ((MulAut.conj (⟨b,hb⟩ : B)) z)
      (((MulAut.conj (⟨b,hb⟩ : B)).orderOf_eq z).trans hz)
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hh)
  apply central _ ((inferInstance : K.Normal).conj_mem b (hBK hb) a)
  have hc := congrArg (MulAut.conj a) hbc
  simpa only [map_mul,MulAut.conj_apply,hzfix] using hc
end Subgroup
