module
public import Theory.Representation.BinaryPlaneCubic
public import Theory.Representation.BinaryOffender.CubicRatio

/-!
# Recognizing a reduced faithful binary plane actor

A faithful binary plane action embeds its actor in the symmetric group on
three points. A finite cubic ratio supplies a nontrivial involution, while
the trivial two-core gives a subgroup of order three. Thus the actor has
order six and the original embedding is an isomorphism.

Source application: Aschbacher--Smith 15.1.2--3, the dimension-two branch,
followed by the rank-two entry in 14.2.4, printed p.982.
-/

public section
open Subgroup Module
namespace Representation.BinaryPlane
open BinaryOffender
variable {D V : Type*} [Group D] [Finite D]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- A faithful binary plane actor with trivial two-core and finite cubic ratio
is the full symmetric-three group. -/
theorem equiv_symmetricThree_of_finite_cubicRatio
    (ρ : Representation (ZMod 2) D V) (hf : Function.Injective ρ)
    (hd : finrank (ZMod 2) V=2) (hcore : pCore 2 D=⊥)
    (hq : cubicRatio ρ≠⊤) : Nonempty (D≃*Equiv.Perm (Fin 3)) := by
  obtain ⟨A,hA,_,_⟩ := (cubicRatio_le_iff ρ hq).mp le_rfl
  let := hA.2
  obtain ⟨t,ht,ht1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  have ht2 : orderOf t=2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian t ht) ht1
  have h2 : 2∣Nat.card D := ht2 ▸ orderOf_dvd_natCard t
  let : Nontrivial D := ⟨⟨t,1,ht1⟩⟩
  obtain ⟨C,_,hC⟩ := exists_normal_cubic ρ hf hd hcore
  have h3 : 3∣Nat.card D := hC ▸ C.card_subgroup_dvd_card
  let f := symmetricThreeHom ρ hd
  have hi : Function.Injective f := symmetricThreeHom_injective ρ hf hd
  have hp : Nat.card (Equiv.Perm (Fin 3))=6 := by
    simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have hdiv : Nat.card D∣6 := hp ▸ card_dvd_of_injective f hi
  have hcard : Nat.card D=6 := Nat.dvd_antisymm hdiv
    ((by decide : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd h2 h3)
  exact ⟨MulEquiv.ofBijective f
    ((Nat.bijective_iff_injective_and_card f).mpr ⟨hi,hcard.trans hp.symm⟩)⟩

end Representation.BinaryPlane
