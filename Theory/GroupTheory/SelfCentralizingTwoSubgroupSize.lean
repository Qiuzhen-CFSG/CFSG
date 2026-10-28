module

public import Theory.GroupTheory.SelfCentralizingNormalFourRecognition

/-!
# A characteristic-two local core has at least four elements

An element of order three acts nontrivially on a self-centralizing normal
two-subgroup. A moved orbit has three elements, all different from the
identity. This excludes characteristic two at the order-six and order-twelve
vertices in Aschbacher–Smith F.6.5, printed p.305.
-/

open Subgroup
public theorem card_ge_four_of_selfCentralizing_normal_two_subgroup
    {G : Type*} [Group G] [Finite G] (Q : Subgroup G) [Q.Normal]
    (hQ : IsPGroup 2 Q) (hcent : centralizer (Q : Set G) ≤ Q)
    (hthree : 3 ∣ Nat.card G) : 4 ≤ Nat.card Q := by
  classical
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := G) 3 hthree
  let b : MulAut Q := MulAut.conjNormal x
  have hb : b ^ 3 = 1 := by
    change (MulAut.conjNormal x) ^ 3 = 1
    rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  have hne : b ≠ 1 := by
    intro he
    have hxc : x ∈ centralizer (Q : Set G) := by
      rw [mem_centralizer_iff]
      intro q hq
      have hh := congrArg (fun a : MulAut Q => (a ⟨q,hq⟩ : G)) he
      change x * q * x⁻¹ = q at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    let z : Q := ⟨x,hcent hxc⟩
    have hz : orderOf z = 3 := (Subgroup.orderOf_coe z).symm.trans hx
    have hh := hQ.orderOf_coprime (by decide : Nat.Coprime 2 3) z
    rw [hz] at hh
    norm_num at hh
  have h3 (w : Q) : b (b (b w)) = w := by
    simpa only [pow_succ,pow_zero,one_mul,MulAut.mul_apply,MulAut.one_apply] using
      congrArg (fun f : MulAut Q => f w) hb
  obtain ⟨w,hw⟩ : ∃ w : Q, b w ≠ w := by
    by_contra! hh
    exact hne (MulEquiv.ext hh)
  have hw1 : w ≠ 1 := by intro hh; subst w; simp at hw
  have hbw1 : b w ≠ 1 := by simpa using hw1
  have hbbw1 : b (b w) ≠ 1 := by simpa using hw1
  have hww : b (b w) ≠ w := by
    intro hh
    exact hw ((congrArg b hh).symm.trans (h3 w))
  have hbw : b (b w) ≠ b w := fun hh => hw (b.injective hh)
  let _ : Fintype Q := Fintype.ofFinite Q
  have hfour : ({1,w,b w,b (b w)} : Finset Q).card = 4 := by
    simp [Ne.symm hw1,Ne.symm hbw1,Ne.symm hbbw1,
      Ne.symm hw,Ne.symm hww,Ne.symm hbw]
  rw [←hfour,Nat.card_eq_fintype_card]
  exact Finset.card_le_univ _
