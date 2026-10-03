module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Characteristic involutions from invariant profiles

A nonconstant function on a three-element set has a singleton fiber. Thus an
automorphism-invariant profile on the three nonidentity elements of a
characteristic elementary four singles out a characteristic subgroup of order
two. Counts of roots of a fixed power give such invariant profiles.

This is an elementary finite-set argument; it requires no classification of
two-groups and makes no assertion that any particular profile is nonconstant.
-/

open Subgroup

private theorem singleton_fiber_of_three {α β : Type*} (S : Set α)
    (hS : S.ncard = 3) (f : α → β)
    (hne : ∃ x ∈ S, ∃ y ∈ S, f x ≠ f y) :
    ∃ z ∈ S, ∀ y ∈ S, f y = f z → y = z := by
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Set.ncard_eq_three.mp hS
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at *
  by_cases h1 : f x = f y
  · by_cases h2 : f x = f z
    · grind
    · exact ⟨z, by simp, by grind⟩
  · by_cases h2 : f x = f z
    · exact ⟨y, by simp, by grind⟩
    · exact ⟨x, by simp, by grind⟩

namespace Subgroup

/-- A nonconstant invariant on the nonidentity elements of a characteristic
elementary four singles out a characteristic involution. -/
public theorem exists_characteristic_two_of_nonconstant_invariant_on_four
    {G α : Type*} [Group G] [Finite G]
    (W : Subgroup G) [W.Characteristic] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4) (f : G → α)
    (hf : ∀ a : MulAut G, ∀ x : G, f (a x) = f x)
    (hne : ∃ x ∈ W, x ≠ 1 ∧ ∃ y ∈ W, y ≠ 1 ∧ f x ≠ f y) :
    ∃ K : Subgroup G, K.Characteristic ∧ Nat.card K = 2 := by
  have hthree : (({1} : Set W)ᶜ).ncard = 3 := by
    rw [Set.ncard_compl, hW, Set.ncard_singleton]
  have hne' : ∃ x ∈ ({1} : Set W)ᶜ, ∃ y ∈ ({1} : Set W)ᶜ,
      f (x : G) ≠ f (y : G) := by
    obtain ⟨x, hx, hx1, y, hy, hy1, hxy⟩ := hne
    exact ⟨⟨x, hx⟩, fun h => hx1 (congrArg Subtype.val h),
      ⟨y, hy⟩, fun h => hy1 (congrArg Subtype.val h), hxy⟩
  obtain ⟨z, hz, hu⟩ := singleton_fiber_of_three _ hthree (fun w : W => f w) hne'
  have hz1 : (z : G) ≠ 1 := fun h => hz (Subtype.ext h)
  have hfix (a : MulAut G) : a (z : G) = z := by
    have hneA : MulAut.characteristic W a z ≠ 1 := by
      intro h
      have hh := (MulAut.characteristic W a).injective (h.trans (map_one _).symm)
      exact hz hh
    exact congrArg Subtype.val (hu (MulAut.characteristic W a z) hneA (hf a z))
  refine ⟨zpowers (z : G), ?_, ?_⟩
  · apply characteristic_iff_map_eq.mpr
    intro a
    rw [MonoidHom.map_zpowers]
    change zpowers (a (z : G)) = zpowers (z : G)
    rw [hfix]
  · rw [Nat.card_zpowers]
    exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian _ z.property) hz1

end Subgroup

/-- Automorphisms preserve the number of roots of each fixed power. -/
public theorem power_fiber_card_aut {G : Type*} [Group G] (k : ℕ)
    (a : MulAut G) (z : G) :
    Nat.card {x : G // x ^ k = a z} = Nat.card {x : G // x ^ k = z} := by
  apply Nat.card_congr
  exact
    { toFun := fun x => ⟨a.symm x, by
        rw [← map_pow, x.property, a.symm_apply_apply]⟩
      invFun := fun x => ⟨a x, by rw [← map_pow, x.property]⟩
      left_inv := fun x => Subtype.ext (a.apply_symm_apply x)
      right_inv := fun x => Subtype.ext (a.symm_apply_apply x) }
