module
public import Theory.SpecificGroups.SL2.ThreeResidualCore
public import Theory.GroupAction.TernaryCubicFixedCard
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Cubic fixed points for a ternary SL₂(3) action

When the central involution of SL₂(3) inverts an elementary ternary group,
the fixed subgroups of two suitable conjugate cubics intersect trivially.
Their product bounds the square of the fixed order by the whole order.
Combined with the cubic displacement filtration, this determines the fixed
order as nine when the group has order81. The only finite calculation is
on the 24-element binary tetrahedral model.

The actual consumer is the opposite-factor action on the marked cubic-core
quotient in G2Recognition.MaximalCoreIntersection, for Aschbacher–Smith
I.4.5, printed p.417. No recognition or simplicity conclusion is assumed.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory
private abbrev BT := QuaternionGroup 2 ⋊[GLS3.Chapter5.SchurPresentation.q8C3Action]
  Multiplicative (ZMod 3)
private instance : DecidableEq BT := SemidirectProduct.equivProd.injective.decidableEq
private instance : Fintype BT := Fintype.ofEquiv _ SemidirectProduct.equivProd.symm

private theorem cubic_pair : ∀ x z : BT, x*x*x=1 → x≠1 → z*z=1 → z≠1 →
    ∃ g : BT, (x*(g*x⁻¹*g⁻¹))*(x*(g*x⁻¹*g⁻¹))=z := by decide +kernel

theorem sl23_inverting_cubic_fixed_bound {L A : Type*} [Group L] [Group A]
    [Finite A] [IsElementaryAbelian 3 A]
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
    (ρ : L →* MulAut A) (x z : L) (hx : orderOf x=3) (hz : orderOf z=2)
    (hzA : ∀ a, ρ z a=a⁻¹) :
    Nat.card (ρ x).fixedSubgroup^2 ≤ Nat.card A := by
  let f := e.trans GLS3.Chapter5.SchurPresentation.binaryTetrahedralEquivSL.symm
  have hx3 : f x*f x*f x=1 := by
    simpa only [f.orderOf_eq, hx, pow_succ, pow_zero, one_mul] using pow_orderOf_eq_one (f x)
  have hz2 : f z*f z=1 := by
    simpa only [←pow_two, f.orderOf_eq, hz] using pow_orderOf_eq_one (f z)
  have hxn : f x≠1 := fun h => by
    have hh := f.orderOf_eq x
    rw [h,orderOf_one,hx] at hh
    omega
  have hzn : f z≠1 := fun h => by
    have hh := f.orderOf_eq z
    rw [h,orderOf_one,hz] at hh
    omega
  obtain ⟨g,hg⟩ := cubic_pair (f x) (f z) hx3 hxn hz2 hzn
  let b := f.symm g
  let y := b*x⁻¹*b⁻¹
  have hxy : (x*y)^2=z := f.injective (by
    simpa only [y,b,map_pow,pow_two,map_mul,map_inv,f.apply_symm_apply] using hg)
  let U := (ρ x).fixedSubgroup
  let W := U.map (ρ b).toMonoidHom
  have hWy (a : A) (ha : a∈W) : ρ y a=a := by
    obtain ⟨u,hu,rfl⟩ := ha
    have hu' : ρ x u=u := (MulAut.mem_fixedSubgroup _ _).mp hu
    have hi : (ρ x)⁻¹ u=u := (ρ x).injective (by simp [hu'])
    change (ρ (b*x⁻¹*b⁻¹)) (ρ b u)=ρ b u
    simp only [map_mul,map_inv,MulAut.mul_apply,MulAut.inv_apply,
      MulEquiv.symm_apply_apply]
    exact congrArg (ρ b) hi
  have hd : Disjoint U W := by
    apply disjoint_iff.mpr
    apply bot_unique
    intro a ha
    have hxa : ρ x a=a := (MulAut.mem_fixedSubgroup _ _).mp ha.1
    have hya := hWy a ha.2
    have hza : ρ z a=a := by
      rw [←hxy,map_pow,pow_two,map_mul]
      change ρ x (ρ y (ρ x (ρ y a)))=a
      rw [hya,hxa,hya,hxa]
    have hi : a⁻¹=a := (hzA a).symm.trans hza
    have h2 : a^2=1 := by
      rw [pow_two]
      calc
        a*a = a⁻¹*a := congrArg (fun v => v*a) hi.symm
        _ = 1 := inv_mul_cancel a
    have h3 : a^3=1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 3 A) a
    have he : a=1 := by simpa only [show 3=2+1 from rfl,pow_succ,h2,one_mul] using h3
    exact he
  have hcard : Nat.card W=Nat.card U := card_map_of_injective (ρ b).injective
  have h := (U⊔W).card_le_card_group
  rw [card_sup_eq_mul_of_normalizes_of_disjoint U W
    (by let : CommGroup A := IsMulCommutative.instCommGroup; exact le_normalizer_of_normal)
    hd,hcard,←pow_two] at h
  exact h

theorem sl23_inverting_cubic_fixed_card_eightyOne {L A : Type*} [Group L] [Group A]
    [Finite A] [IsElementaryAbelian 3 A]
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
    (ρ : L →* MulAut A) (x z : L) (hx : orderOf x=3) (hz : orderOf z=2)
    (hzA : ∀ a, ρ z a=a⁻¹) (hA : Nat.card A=81) :
    Nat.card (ρ x).fixedSubgroup=9 := by
  have hu := sl23_inverting_cubic_fixed_bound e ρ x z hx hz hzA
  have hl := (ρ x).ternary_cubic_fixed_card_bound (by
    rw [←map_pow,show x^3=1 from hx ▸ pow_orderOf_eq_one x,map_one])
  have hd := (ρ x).fixedSubgroup.card_subgroup_dvd_card
  rw [hA] at hu hl hd
  obtain ⟨k,hk,he⟩ := (Nat.dvd_prime_pow Nat.prime_three (m:=4)).mp hd
  interval_cases k <;> rw [he] at hu hl ⊢ <;> norm_num at *
end Theory.GroupTheory
