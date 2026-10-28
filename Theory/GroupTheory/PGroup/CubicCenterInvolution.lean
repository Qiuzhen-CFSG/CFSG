module
public import Theory.ElementaryAbelian.Extraspecial
public import Theory.GroupTheory.OddFixedKernelInvolution
public import Theory.GroupTheory.ClassTwoCommutator

/-!
# An involution fixing exactly a cubic center

An involutory automorphism whose fixed subgroup is the center of order
three inverts the central quotient. Thus commutators are central. Their
order divides three, so the central quotient is elementary abelian.
The same automorphism fixes each cube and inverts it, forcing exponent
three. A proper center therefore makes the group extraspecial.

This elementary extension of the odd-fixed-kernel argument is used in
Aschbacher–Smith I.4.5's order-243 Sylow exclusion. The fixed-kernel
inversion argument is the standard one recorded in
`Theory.GroupTheory.OddFixedKernelInvolution`.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace MulAut
variable {P : Type*} [Group P] [Finite P]

/-- An involution fixing exactly a cubic center forces an extraspecial group of exponent three. -/
theorem extraspecial_three_of_fixed_center (a : MulAut P)
    (ha : Function.Involutive a) (hz : Nat.card (center P)=3)
    (hne : center P≠⊤) (hf : ∀ x, a x=x ↔ x∈center P) :
    IsExtraspecial 3 P ∧ (∀ x : P, x^3=1) ∧ _root_.commutator P≤center P := by
  obtain ⟨hinv,hclass⟩ := a.quotient_inversion_of_odd_fixed_kernel ha (center P)
    (by rw [hz]; decide) hf
  have hcube (x : P) : x^3∈center P := by
    apply mem_center_iff.mpr
    intro y
    apply commutatorElement_eq_one_iff_mul_comm.mp
    have hcomm : ⁅y,x⁆∈center P := hclass (commutator_mem_commutator (mem_top _) (mem_top _))
    have hp : ⁅y,x⁆^3=1 := orderOf_dvd_iff_pow_eq_one.mp
      (hz ▸ (center P).orderOf_dvd_natCard hcomm)
    have hh : Subgroup.ClassTwo.commutatorHom hclass y (x^3)=1 := by
      rw [map_pow]
      exact hp
    exact hh
  have hquot : IsElementaryAbelian 3 (P ⧸ center P) := {
    toIsMulCommutative := Normal.quotient_commutative_iff_commutator_le.mpr hclass
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro x
      obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (center P) x
      rw [←map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (hcube x)) }
  refine ⟨⟨hz,hquot,QuotientGroup.nontrivial_iff.mpr hne⟩,?_,hclass⟩
  intro x
  have hw : (a x*x)^3=1 := orderOf_dvd_iff_pow_eq_one.mp
    (hz ▸ (center P).orderOf_dvd_natCard (hinv x))
  have hcomm : Commute (a x) x := by
    have hh := mem_center_iff.mp (hinv x) x
    exact mul_right_cancel (by simpa only [mul_assoc] using hh.symm)
  rw [hcomm.mul_pow,←map_pow,(hf _).mpr (hcube x)] at hw
  have hx2 : (⟨x^3,hcube x⟩ : center P)^2=1 := Subtype.ext ((pow_two _).trans hw)
  have hx1 : (⟨x^3,hcube x⟩ : center P)=1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 3 2)
      (by simpa only [hz] using orderOf_dvd_natCard (⟨x^3,hcube x⟩ : center P))
      (orderOf_dvd_of_pow_eq_one hx2))
  exact congrArg Subtype.val hx1

end MulAut
