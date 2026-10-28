module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Cyclic subgroups of finite quotients

A finite group contains an isomorphic copy of each cyclic subgroup of any
quotient. Lift a generator, then take a power whose order is the order of the
cyclic subgroup. This does not assert that the quotient map splits on that
subgroup: the constructed copy need not map isomorphically onto it.

This elementary order argument applies in particular to tori in central
quotients, without imposing an unjustified splitting condition on the cover.
-/

@[expose] public section
namespace Theory.GroupTheory
open Subgroup

/-- An embedding of a cyclic group in a finite quotient gives an embedding
upstairs. The new embedding is not asserted to be a section of the quotient. -/
theorem cyclic_injective_of_surjective
    {C A B : Type*} [Group C] [IsCyclic C] [Group A] [Finite A] [Group B]
    (q : A →* B) (hq : Function.Surjective q)
    (i : C →* B) (hi : Function.Injective i) :
    ∃ j : C →* A, Function.Injective j := by
  obtain ⟨c, hc⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := C)
  obtain ⟨a, ha⟩ := hq (i c)
  have hd : Nat.card C ∣ orderOf a := by
    rw [← hc, ← orderOf_injective i hi, ← ha]
    exact orderOf_map_dvd q a
  let b := a ^ (orderOf a / Nat.card C)
  have hb : orderOf b = Nat.card C :=
    orderOf_pow_orderOf_div (orderOf_pos a).ne' hd
  let e : C ≃* zpowers b := mulEquivOfCyclicCardEq (by rw [Nat.card_zpowers, hb])
  exact ⟨(zpowers b).subtype.comp e.toMonoidHom,
    (zpowers b).subtype_injective.comp e.injective⟩

end Theory.GroupTheory
