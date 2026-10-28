module
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.PGroup

/-!
# Odd complements inside a semidirect product with a two-group actor

An injective homomorphism from a finite group H into X semidirect A
identifies H with a subgroup D of the left factor when the following
conditions hold: A is a two-group, H has a normal subgroup L with an
odd-order complement E, the image of L is exactly the left copy of D,
and the image of E lies in the right actor.

The right projection restricts to an injection of E into A. An odd-order
two-group is trivial, so E is trivial and L is all of H. The original
injective map then supplies the actual equivalence with D.

This elementary coprime argument is used in the characteristic-three
specialization of ABG II.3 Proposition 3. The theorem is independent of
that application and uses only Mathlib group APIs.
-/

namespace SemidirectProduct

/-- An odd complement mapping into a two-group actor is trivial, yielding the left-factor model. -/
public theorem equiv_of_odd_complement_two_actor
    {H X A : Type*} [Group H] [Finite H] [Group X] [Group A]
    (α : A →* MulAut X) (hA : IsPGroup 2 A) (D : Subgroup X)
    (L E : Subgroup H) [L.Normal] (hc : L.IsComplement' E) (ho : Odd (Nat.card E))
    (f : H →* X ⋊[α] A) (hf : Function.Injective f)
    (hL : L.map f = D.map SemidirectProduct.inl)
    (hE : E.map f ≤ (SemidirectProduct.inr : A →* X ⋊[α] A).range) :
    Nonempty (H ≃* D) := by
  let c : E →* A := SemidirectProduct.rightHom.comp (f.comp E.subtype)
  have heq (e : E) : f e = SemidirectProduct.inr (c e) := by
    obtain ⟨a, ha⟩ := hE (Subgroup.mem_map_of_mem f e.property)
    have hh := congrArg (fun z : X ⋊[α] A => z.right) ha
    change a = c e at hh
    exact ha.symm.trans (congrArg SemidirectProduct.inr hh)
  have hci : Function.Injective c := by
    intro a b hab
    apply Subtype.ext
    apply hf
    rw [heq, heq, hab]
  have hcE : Nat.card E = 1 := by
    rcases (hA.of_injective c hci).card_eq_or_dvd with h | h
    · exact h
    · exact (ho.not_two_dvd_nat h).elim
  have hbot : E = ⊥ := Subgroup.eq_bot_of_card_eq _ hcE
  have htop : L = ⊤ := by simpa only [hbot, sup_bot_eq] using hc.sup_eq_top
  let eL : L ≃* D := (L.equivMapOfInjective f hf).trans
    ((MulEquiv.subgroupCongr hL).trans
      (D.equivMapOfInjective SemidirectProduct.inl SemidirectProduct.inl_injective).symm)
  exact ⟨Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr htop.symm).trans eL)⟩

end SemidirectProduct
