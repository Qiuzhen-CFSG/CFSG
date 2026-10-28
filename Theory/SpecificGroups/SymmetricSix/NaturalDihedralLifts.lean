module

public import Theory.SpecificGroups.SymmetricSix.NaturalExtensionLifts
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.CommutingSwap

/-!
# A simultaneous dihedral relation in the original polar extension

Two commuting involutory lifts with the same kernel fixed space are retained.
An involution interchanging their quotient images lifts to an involution.
Its conjugate of the first lift differs from the second by a kernel element
fixed by both; this forces the actual fourth-power relation. No complement
of the whole alternating-six extension is assumed.
-/

public noncomputable section
namespace Theory.SpecificGroups.SymmetricSix.NaturalExtensionLifts
open scoped Matrix
variable {G : Type*} [Group G]

/-- Equal kernel fixed spaces force a simultaneous commutation relation
between a retained involution and its corrected conjugate. -/
theorem commute_conjugate_of_same_kernel_fixed
    (q : G→*A6) (hk : ∀ a∈q.ker,a^2=1)
    (x y s : G) (hx2 : x^2=1) (hy2 : y^2=1) (hs2 : s^2=1)
    (hxy : Commute x y) (hsq : q (s*x*s⁻¹)=q y)
    (hfixed : ∀ a∈q.ker,Commute a y → Commute a x) :
    Commute x (s*x*s⁻¹) ∧ (x*s)^4=1 := by
  let z := s*x*s⁻¹
  let a := z*y⁻¹
  have ha : a∈q.ker := by
    change q (s*x*s⁻¹*y⁻¹)=1
    rw [map_mul,hsq,map_inv,mul_inv_cancel]
  have ha2 := hk a ha
  have hz2 : z^2=1 := by
    change (MulAut.conj s x)^2=1
    rw [←map_pow,hx2,map_one]
  have hai : a⁻¹=a := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using ha2)
  have hyi : y⁻¹=y := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hy2)
  have hzi : z⁻¹=z := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hz2)
  have haz : a*y=z := by dsimp [a]; group
  have hay : Commute a y := by
    change a*y=y*a
    calc
      a*y=z := haz
      _=z⁻¹ := hzi.symm
      _=(a*y)⁻¹ := congrArg Inv.inv haz.symm
      _=y*a := by rw [mul_inv_rev,hyi,hai]
  have hax := hfixed a ha hay
  have hxz : Commute x z := by rw [←haz]; exact hax.symm.mul_right hxy
  have hsi : s⁻¹=s := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hs2)
  have h4 : (x*s)^4=1 := calc
    (x*s)^4=(x*z)^2 := by
      dsimp [z]
      rw [hsi,show (4:Nat)=2*2 from rfl,pow_mul]
      congr 1
      simp only [pow_two,mul_assoc]
    _=x^2*z^2 := hxz.mul_pow 2
    _=1 := by rw [hx2,hz2,one_mul]
  exact ⟨hxz,h4⟩

/-- The actual quotient and polar kernel produce an involutory swapping
lift and the dihedral fourth-power relation on the retained first actor. -/
theorem exists_dihedral_lift_of_same_kernel_fixed
    (q : G→*A6) (hq : Function.Surjective q)
    (e : q.ker≃*Multiplicative NaturalModule)
    (he : ∀ (g : G) (v : q.ker), e (MulAut.conjNormal g v)=
      Multiplicative.ofAdd ((polarRepresentation (q g).val).val *ᵥ (e v).toAdd))
    (x y : G) (hx2 : x^2=1) (hy2 : y^2=1) (hxy : Commute x y)
    (hqx : orderOf (q x)=2) (hqy : orderOf (q y)=2) (hne : q x≠q y)
    (hfixed : ∀ a∈q.ker,Commute a y → Commute a x) :
    ∃ s : G, orderOf s=2 ∧ orderOf (q s)=2 ∧
      q (s*x*s⁻¹)=q y ∧ Commute x (s*x*s⁻¹) ∧ (x*s)^4=1 ∧
      orderOf (q (x*s))=4 := by
  obtain ⟨t,ht,htxy⟩ := AlternatingSix.ShadowLocal.exists_involutory_swap
    (q x) (q y) hqx hqy (hxy.map q) hne
  obtain ⟨b,hb⟩ := hq t
  obtain ⟨p,hp2,hpq⟩ := correct_involution_lift q e he b (hb ▸ ht)
  let s := (p:G)*b
  have hsq : q s=t := hpq.trans hb
  have hs1 : s≠1 := by intro hh; rw [←hsq,hh,map_one,orderOf_one] at ht; omega
  have hs2 : s^2=1 := hp2
  have hconj : q (s*x*s⁻¹)=q y := by rw [map_mul,map_mul,map_inv,hsq,htxy]
  have hk (a : G) (ha : a∈q.ker) : a^2=1 := by
    have h : (⟨a,ha⟩:q.ker)^2=1 := by
      apply e.injective
      rw [map_pow,map_one]
      apply Multiplicative.toAdd.injective
      rw [pow_two]
      change (e ⟨a,ha⟩).toAdd+(e ⟨a,ha⟩).toAdd=0
      funext i
      exact CharTwo.add_self_eq_zero _
    exact congrArg Subtype.val h
  obtain ⟨hc,h4⟩ := commute_conjugate_of_same_kernel_fixed q hk x y s hx2 hy2 hs2 hxy hconj hfixed
  have hqi : (q s)⁻¹=q s := inv_eq_of_mul_eq_one_right
    (by rw [←map_mul,←pow_two,hs2,map_one])
  have hprod : q (x*s)^2=q x*q y := by
    rw [map_mul,pow_two]
    have hh : q s*q x*q s=q y := by
      simpa only [map_mul,map_inv,hqi] using hconj
    calc
      _=q x*(q s*q x*q s) := by group
      _=q x*q y := by rw [hh]
  have hne2 : q (x*s)^2≠1 := by
    rw [hprod]
    intro hh
    apply hne
    have hxi : (q x)⁻¹=q x := inv_eq_of_mul_eq_one_right
      (by rw [←map_mul,←pow_two,hx2,map_one])
    exact hxi.symm.trans (inv_eq_of_mul_eq_one_right hh)
  have hqo : orderOf (q (x*s))=4 :=
    GLS3.Chapter5.SchurPresentation.orderOf_eq_four_of_sq_ne_one_of_pow_four_eq_one
      _ (by rw [←map_pow,h4,map_one]) hne2
  exact ⟨s,orderOf_eq_prime hs2 hs1,hsq ▸ ht,hconj,hc,h4,hqo⟩

end Theory.SpecificGroups.SymmetricSix.NaturalExtensionLifts
