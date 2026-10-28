module

public import Theory.Representation.BinaryPermutation.SymmetricEightTransvections
public import Theory.Representation.BinaryPermutation.Faithful
public import Theory.Representation.BinaryPermutationNaturalStructure
public import Theory.ElementaryAbelian.Basic

/-!
# Groups of transvections on the eight-point core

The seven-dimensional binary core is faithful. In its symmetric-group
action, an involution with displacement at most one is a transposition,
by the intrinsic transvection theorem. Therefore sign is injective on any
elementary subgroup all of whose elements have displacement at most one,
and that subgroup has order at most two.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 12.6.23, printed p.830, the bound on the reverse centralizer index.
-/

public section

open Subgroup
namespace BinaryPermutation.EightTransvectionActors

theorem core_faithful : Function.Injective (coreRepresentation (Fin 8)) := by
  intro g h he
  apply naturalRepresentation_injective (Fin 8) (by decide)
  apply LinearMap.ext
  intro v
  obtain ⟨u, rfl⟩ := coreToNatural_surjective v
  rw [← coreToNatural_equivariant, ← coreToNatural_equivariant, he]

private theorem swap_of_small_displacement (a : Equiv.Perm (Fin 8))
    (ha : a ≠ 1) (ha2 : a ^ 2 = 1)
    (hd : Module.finrank (ZMod 2) (coreRepresentation (Fin 8) a - LinearMap.id).range ≤ 1) :
    a.IsSwap := by
  let φ : Equiv.Perm (Fin 8) →* (core (Fin 8) ≃ₗ[ZMod 2] core (Fin 8)) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (core (Fin 8))).toMonoidHom.comp
      (coreRepresentation (Fin 8)).asGroupHom
  have hφ : Function.Injective φ := fun x y h =>
    core_faithful (congrArg LinearEquiv.toLinearMap h)
  exact Representation.SymmetricEightTransvections.isSwap_of_transvection φ hφ a ha ha2
    (Representation.SymmetricEightTransvections.Linear.of_small_displacement (φ a) hd)

theorem card_le_two_of_small_displacements (A : Subgroup (Equiv.Perm (Fin 8)))
    [IsElementaryAbelian 2 A]
    (hd : ∀ a ∈ A, Module.finrank (ZMod 2)
      (coreRepresentation (Fin 8) a - LinearMap.id).range ≤ 1) : Nat.card A ≤ 2 := by
  let s : A →* ℤˣ := Equiv.Perm.sign.comp A.subtype
  have hs : Function.Injective s := by
    apply (injective_iff_map_eq_one _).mpr
    intro a ha
    by_contra hne
    have hswap := swap_of_small_displacement a.val
      (fun he => hne (Subtype.ext he))
      (elemPow_eq_one_of_isElementaryAbelian a.val a.property) (hd a a.property)
    have he : Equiv.Perm.sign a.val = 1 := ha
    rw [hswap.sign_eq] at he
    exact (by decide : (-1 : ℤˣ) ≠ 1) he
  have h := Nat.card_le_card_of_injective s hs
  have hc : Nat.card ℤˣ = 2 := by rw [Nat.card_eq_fintype_card]; decide
  rwa [hc] at h
end BinaryPermutation.EightTransvectionActors
