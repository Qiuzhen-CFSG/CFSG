module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.Tactic.NormNum

/-!
# Centralizers of elements of order three in S5

A three-cycle has six commuting permutations. A finite group embedded in
its centralizer therefore has order dividing six. In particular S5 has no
abelian subgroup of order twelve: Cauchy's theorem would put such a subgroup
inside the centralizer of one of its elements of order three.

The commuting-permutation count is checked by kernel reduction on the actual
permutation group. The divisibility argument is ordinary Lagrange theory.

Source application: Z. Janko, *A characterization of the Mathieu simple
groups, I*, J. Algebra 9 (1968), Section 2, Lemma 6, p.7.
-/

open Subgroup
namespace Theory.SpecificGroups.SymmetricFive

private theorem commuting_count : ∀ x : Equiv.Perm (Fin 5), x ^ 3 = 1 → x ≠ 1 →
    (Finset.univ.filter fun y : Equiv.Perm (Fin 5) => y * x = x * y).card = 6 := by
  decide +kernel

/-- The centralizer of an element of order three in S5 has order six. -/
public theorem centralizer_three_card (x : Equiv.Perm (Fin 5)) (hx : orderOf x = 3) :
    Nat.card (centralizer ({x} : Set (Equiv.Perm (Fin 5)))) = 6 := by
  classical
  have hcount := commuting_count x ((orderOf_eq_prime_iff.mp hx).1)
    ((orderOf_eq_prime_iff.mp hx).2)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simpa only [mem_centralizer_singleton_iff] using hcount

/-- A group faithfully commuting with a three-cycle has order dividing six. -/
public theorem card_dvd_six_of_centralizes_three {A : Type*} [Group A]
    (x : Equiv.Perm (Fin 5)) (hx : orderOf x = 3)
    (f : A →* Equiv.Perm (Fin 5)) (hf : Function.Injective f)
    (hc : ∀ a, f a * x = x * f a) : Nat.card A ∣ 6 := by
  let g : A →* centralizer ({x} : Set (Equiv.Perm (Fin 5))) :=
    f.codRestrict _ (fun a => mem_centralizer_singleton_iff.mpr (hc a))
  have hg : Function.Injective g := fun a b h => hf (congrArg Subtype.val h)
  have h := Subgroup.card_dvd_of_injective g hg
  rwa [centralizer_three_card x hx] at h

/-- The elementary obstruction at the end of Janko's order-168 branch. -/
public theorem no_abelian_subgroup_card_twelve (A : Subgroup (Equiv.Perm (Fin 5)))
    [IsMulCommutative A] : Nat.card A ≠ 12 := by
  intro hA
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := A) 3 (by rw [hA]; decide)
  have hx' : orderOf (x : Equiv.Perm (Fin 5)) = 3 :=
    (orderOf_injective A.subtype Subtype.val_injective x).trans hx
  have h := card_dvd_six_of_centralizes_three (x : Equiv.Perm (Fin 5)) hx'
    A.subtype Subtype.val_injective (fun a => congrArg Subtype.val (mul_comm' a x))
  rw [hA] at h
  norm_num at h

end Theory.SpecificGroups.SymmetricFive
