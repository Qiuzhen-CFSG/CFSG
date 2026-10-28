module
public import Theory.GroupTheory.PGroup.CyclicInvolution
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.Tactic.Group
/-!
# Central involutions over a quaternion kernel

Let a homomorphism have quaternion kernel and finite cyclic image group.
A noncentral involutory lift forces every central involution to equal the
kernel's unique involution. Otherwise its image equals the noncentral lift's
image, and their quotient is an involution in the quaternion kernel. That
quotient is central, contradicting the chosen lift's noncentral action.

Source application: Aschbacher--Smith J.3.6, printed p.439, for the actual
order32 subgroup of N_H(B₅) acting on B₅.
-/

public section
open Subgroup
namespace Subgroup

private theorem quaternion_involution_unique (x y : QuaternionGroup 2)
    (hx : x^2=1 ∧ x≠1) (hy : y^2=1 ∧ y≠1) : x=y := by
  have h : ∀ a b : QuaternionGroup 2, a^2=1 ∧ a≠1 → b^2=1 ∧ b≠1 → a=b := by decide +kernel
  exact h x y hx hy

private theorem quaternion_square_one_central (x y : QuaternionGroup 2)
    (hx : x^2=1) : y*x=x*y := by
  have h : ∀ a b : QuaternionGroup 2, a^2=1 → b*a=a*b := by decide +kernel
  exact h x y hx

/-- A cyclic quotient and a noncentral involutory lift force the unique central
involution to be the quaternion kernel's involution. -/
theorem central_involution_eq_of_quaternion_kernel
    {R A : Type*} [Group R] [Group A] [Finite A] [IsCyclic A]
    (f : R →* A) (e : f.ker ≃* QuaternionGroup 2)
    (z i : R) (hzK : z∈f.ker) (hz : orderOf z=2) (hi : orderOf i=2)
    (hinon : i∉centralizer (f.ker : Set R))
    (j : R) (hj : j∈center R) (hj2 : orderOf j=2) : j=z := by
  have hcentral {x : R} (hxK : x∈f.ker) (hx2 : x^2=1) :
      x∈centralizer (f.ker : Set R) := by
    intro y hy
    have hxs : (⟨x,hxK⟩ : f.ker)^2=1 := Subtype.ext hx2
    have he := quaternion_square_one_central (e ⟨x,hxK⟩) (e ⟨y,hy⟩)
      (by rw [← map_pow,hxs,map_one])
    have hh : (⟨y,hy⟩ : f.ker)*⟨x,hxK⟩=⟨x,hxK⟩*⟨y,hy⟩ :=
      e.injective ((map_mul e _ _).trans (he.trans (map_mul e _ _).symm))
    exact congrArg Subtype.val hh
  have hfi : f i≠1 := fun h => hinon (hcentral h (orderOf_eq_prime_iff.mp hi).1)
  by_cases hjf : f j=1
  · have hzK2 : (⟨z,hzK⟩ : f.ker)^2=1 := Subtype.ext (orderOf_eq_prime_iff.mp hz).1
    have hjK2 : (⟨j,hjf⟩ : f.ker)^2=1 := Subtype.ext (orderOf_eq_prime_iff.mp hj2).1
    have he := quaternion_involution_unique (e ⟨j,hjf⟩) (e ⟨z,hzK⟩)
      ⟨by rw [← map_pow,hjK2,map_one],by
        intro hh
        have hh' := congrArg Subtype.val (e.injective (hh.trans (map_one e).symm))
        exact (orderOf_eq_prime_iff.mp hj2).2 hh'⟩
      ⟨by rw [← map_pow,hzK2,map_one],by
        intro hh
        have hh' := congrArg Subtype.val (e.injective (hh.trans (map_one e).symm))
        exact (orderOf_eq_prime_iff.mp hz).2 hh'⟩
    exact congrArg Subtype.val (e.injective he)
  · have hfji : f j=f i := IsCyclic.eq_of_orderOf_eq_two
      (orderOf_eq_prime (by rw [← map_pow,(orderOf_eq_prime_iff.mp hj2).1,map_one]) hjf)
      (orderOf_eq_prime (by rw [← map_pow,(orderOf_eq_prime_iff.mp hi).1,map_one]) hfi)
    have htK : j*i⁻¹∈f.ker := by
      change f (j*i⁻¹)=1
      rw [map_mul,map_inv,hfji,mul_inv_cancel]
    have ht2 : (j*i⁻¹)^2=1 := by
      have hc : Commute j i⁻¹ := (mem_center_iff.mp hj i⁻¹).symm
      rw [hc.mul_pow,(orderOf_eq_prime_iff.mp hj2).1,inv_pow,
        (orderOf_eq_prime_iff.mp hi).1,inv_one,mul_one]
    have hjC : j∈centralizer (f.ker : Set R) := fun x _ => mem_center_iff.mp hj x
    have hc := (centralizer (f.ker : Set R)).mul_mem
      ((centralizer (f.ker : Set R)).inv_mem (hcentral htK ht2)) hjC
    have he : (j*i⁻¹)⁻¹*j=i := by group
    exact (hinon (he ▸ hc)).elim

end Subgroup
