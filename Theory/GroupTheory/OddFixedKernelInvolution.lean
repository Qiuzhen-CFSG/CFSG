module

public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Mathlib.GroupTheory.FixedPointFree
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Quotient inversion from an odd fixed kernel

If an involutory automorphism has an odd normal subgroup as its exact fixed
 subgroup, its action on the quotient is fixed-point free and hence inversion.
 For a fixed quotient coset, the displacement lies in the fixed kernel and is
 also inverted; odd order kills that displacement. This proves the fixed-free
 claim without a separately chosen fixed lift.

The source applications are the actual odd layers modulo X and W in
Aschbacher, *Sporadic Groups* (1994), Lemmas 45.7–45.8, pp.245–246.
-/

public section
open Subgroup
open scoped commutatorElement
namespace MulAut
variable {D : Type*} [Group D] [Finite D]

theorem quotient_inversion_of_odd_fixed_kernel (a : MulAut D)
    (ha : Function.Involutive a) (C : Subgroup D) [C.Normal]
    (hC : Odd (Nat.card C))
    (hf : ∀x, a x=x ↔ x∈C) :
    (∀x, (a x)*x∈C) ∧ _root_.commutator D ≤ C := by
  have hcfix (x : C) : a x=x := (hf x).mpr x.property
  have hmap : C.map a.toMonoidHom = C := by
    apply le_antisymm
    · rintro x ⟨y,hy,rfl⟩
      change a y ∈ C
      rwa [(hf y).mpr hy]
    · intro x hx
      exact ⟨x,hx,(hf x).mpr hx⟩
  let b : MulAut (D ⧸ C) := QuotientGroup.congr C C a hmap
  let q := QuotientGroup.mk' C
  have hb (x : D) : b (q x) = q (a x) := rfl
  have hb2 : Function.Involutive b := by
    intro y
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective C y
    rw [hb,hb,ha]
  have hfree : MonoidHom.FixedPointFree b := by
    intro y hy
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective C y
    have hm : (a x)⁻¹*x∈C := QuotientGroup.eq.mp hy
    let c : C := ⟨(a x)⁻¹*x,hm⟩
    have hc : (c:D)=(c:D)⁻¹ := by
      have hh := hcfix c
      change a ((a x)⁻¹*x)=(a x)⁻¹*x at hh
      change (a x)⁻¹*x=((a x)⁻¹*x)⁻¹
      rw [map_mul,map_inv,ha x] at hh
      simpa only [mul_inv_rev,inv_inv] using hh.symm
    have hc2 : c^2=1 := by
      apply Subtype.ext
      change (c:D)^2=1
      calc
        (c:D)^2 = (c:D)*(c:D)⁻¹ := by rw [pow_two,←hc]
        _ = 1 := mul_inv_cancel _
    have hc1 : c=1 := orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes hC.coprime_two_right
        (orderOf_dvd_natCard c) (orderOf_dvd_of_pow_eq_one hc2))
    have hax : a x=x := by
      have hh := congrArg Subtype.val hc1
      change (a x)⁻¹*x=1 at hh
      exact inv_mul_eq_one.mp hh
    exact QuotientGroup.eq_one_iff x |>.mpr ((hf x).mp hax)
  have hinv (x : D) : q (a x) = (q x)⁻¹ :=
    (hb x).symm.trans (congrFun (hfree.coe_eq_inv_of_involutive hb2) (q x))
  constructor
  · intro x
    apply (QuotientGroup.eq_one_iff _).mp
    change q ((a x)*x)=1
    rw [map_mul,hinv,inv_mul_cancel]
  · change ⁅(⊤ : Subgroup D),⊤⁆ ≤ C
    apply commutator_le.mpr
    intro x _ y _
    apply (QuotientGroup.eq_one_iff _).mp
    change q ⁅x,y⁆=1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (hfree.commute_all_of_involutive hb2 (q x) (q y))

end MulAut
