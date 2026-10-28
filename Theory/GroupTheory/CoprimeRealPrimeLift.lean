module
public import Theory.GroupTheory.CoprimePrimeFusion

/-!
# Lifting a real prime-order element through a coprime kernel

A cyclic prime subgroup lifts isomorphically by Sylow selection in its
preimage. Coprime fusion then lifts conjugacy with the inverse, retaining
the prescribed quotient element. The inverter need not be an involution.

Source application: the full nonsingular point automizer in
Aschbacher--Smith 12.1.1, printed p.788.
-/

public section
open Subgroup

namespace MonoidHom
theorem exists_real_prime_lift
    {G H : Type*} [Group G] [Finite G] [Group H]
    {p : ℕ} [Fact p.Prime] (f : G →* H) (hf : Function.Surjective f)
    (hk : Nat.Coprime p (Nat.card f.ker))
    (y : H) (hy : orderOf y = p) (hr : IsConj y y⁻¹) :
    ∃ x : G, orderOf x = p ∧ f x = y ∧ IsConj x x⁻¹ := by
  let : IsElementaryAbelian p (zpowers y) := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := by
      rw [← hy, ← Nat.card_zpowers]
      exact Group.exponent_dvd_nat_card }
  obtain ⟨A,hA,hm,_⟩ := exists_elementaryAbelian_map_eq_of_surjective_coprime f hf hk (zpowers y)
  let := hA
  obtain ⟨x,hx,hxy⟩ := hm.symm ▸ mem_zpowers y
  have hi := injective_comp_subtype_of_coprime_ker f hk A (IsElementaryAbelian.isPGroup p A)
  have ho : orderOf x = p := by
    have he := orderOf_injective (f.comp A.subtype) hi (⟨x,hx⟩ : A)
    change orderOf (f x) = orderOf (⟨x,hx⟩ : A) at he
    rw [← Subgroup.orderOf_coe,hxy,hy] at he
    exact he.symm
  refine ⟨x,ho,hxy,?_⟩
  apply f.isConj_of_map_isConj_of_prime_order_of_coprime_ker hf hk ho
    (by rw [orderOf_inv,ho])
  simpa only [map_inv,hxy] using hr
end MonoidHom

