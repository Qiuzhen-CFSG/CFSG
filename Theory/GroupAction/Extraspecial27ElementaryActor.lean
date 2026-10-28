module
public import Theory.GroupAction.Extraspecial27InvolutionFixed
public import Theory.GroupAction.KleinFourFactorization

/-!
# Elementary center-preserving actors on extraspecial order27

A finite elementary two-group acting faithfully by automorphisms on an
extraspecial group F of order27, while fixing its center pointwise, has
order at most two. The original action homomorphism remains explicit.

If the actor had more than two elements, choose distinct nonidentity
commuting involutions a and b. Faithfulness makes their images and the
image of ab nonidentity. Each has fixed subgroup exactly Z(F), by the
preceding center-preserving involution theorem. The three-fixed-subgroup
factorization of the odd group F therefore gives F=Z(F), contradicting
orders27 and3.

This is the elementary actor bound in the last extraspecial-module step
of Stellmacher (9.1), Journal of Algebra190 (1997), p.48. No recognition
of a symplectic or quaternion automorphism group is needed.
-/
namespace MulAut
public theorem elementary_two_center_preserving_card_le_two
    {F A : Type*} [Group F] [Finite F] [IsExtraspecial 3 F]
    [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (hF : Nat.card F = 27) (action : A →* MulAut F) (hinj : Function.Injective action)
    (hcenter : ∀ a : A, ∀ z ∈ Subgroup.center F, action a z = z) :
    Nat.card A ≤ 2 := by
  by_contra hsmall
  have hlarge : 3 ≤ Nat.card A := by omega
  let _ : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a,hane⟩ := exists_ne (1 : A)
  obtain ⟨b,hbne,hba⟩ := ENat.exists_ne_ne_of_three_le (α := A)
    (by rw [ENat.card_eq_coe_natCard]; exact_mod_cast hlarge) 1 a
  have square (c : A) : c ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 A) c
  have invol (c : A) : Function.Involutive (action c) := by
    intro x
    have hh := congrArg action (square c)
    rw [map_pow, map_one, pow_two] at hh
    exact congrArg (fun j : MulAut F => j x) hh
  have hcomm : Commute a b := IsMulCommutative.is_comm.comm a b
  have habne : a * b ≠ 1 := by
    intro heq
    apply hba
    have haInv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using square a)
    exact (eq_inv_of_mul_eq_one_right heq).trans haInv
  have hfix (c : A) (hc : c ≠ 1) : fixedSubgroup (action c) = Subgroup.center F :=
    fixed_eq_center_of_extraspecial27_involution hF (action c) (invol c)
      (fun hh => hc (hinj (hh.trans action.map_one.symm))) (hcenter c)
  have hodd : Odd (Nat.card F) := by rw [hF]; decide
  have hall : (⊤ : Subgroup F) ≤ Subgroup.center F := by
    intro x hx
    obtain ⟨x0,x1,x2,h0,h1,h2,hprod⟩ := exists_fixed_mul_fixed_mul_fixed_of_odd_card
      hodd (action a) (action b) (invol a) (invol b) (hcomm.map action) x
    rw [hprod]
    have hm0 : x0 ∈ Subgroup.center F := (hfix a hane).le ((mem_fixedSubgroup _ _).mpr h0)
    have hm1 : x1 ∈ Subgroup.center F := (hfix b hbne).le ((mem_fixedSubgroup _ _).mpr h1)
    have hm2 : x2 ∈ Subgroup.center F := (hfix (a*b) habne).le
      ((mem_fixedSubgroup _ _).mpr (by simpa only [map_mul] using h2))
    exact (Subgroup.center F).mul_mem ((Subgroup.center F).mul_mem hm0 hm1) hm2
  have hZeq : Subgroup.center F = ⊤ := top_unique hall
  have hc := IsExtraspecial.center_order_p 3 F
  rw [hZeq, Subgroup.card_top, hF] at hc
  omega
end MulAut
