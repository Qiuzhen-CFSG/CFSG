module

public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.GroupTheory.Index

/-!
# Cardinality of a pointwise automorphism fixer

For a subgroup P of a finite group G, the inner automorphisms fixing P
are the image of C_G(P). The quotient of the full fixer by its inner
automorphisms embeds in Out(G). Consequently its order is at most
|C_G(P)| |Out(G)|. No centerlessness or splitting is required.

This elementary reduction is used for the M₁₂–A₅ calculation in
Aschbacher–Smith 16.3.5, combined manuscript of 1 March 2004, printed p.1178.
It concerns the full abstract automorphism group.
-/

namespace MulAut
open Subgroup

/-- Bound the full pointwise fixer by the inner centralizer and the actual
outer automorphism index. -/
public theorem card_fixingSubgroup_le_centralizer_mul_outer_index
    {G : Type*} [Group G] [Finite G] (P : Subgroup G) :
    Nat.card (fixingSubgroup (MulAut G) (P : Set G)) ≤
      Nat.card (centralizer (P : Set G)) * (innerSubgroup G).index := by
  let F := fixingSubgroup (MulAut G) (P : Set G)
  let I := (innerSubgroup G).subgroupOf F
  let C := centralizer (P : Set G)
  have hf (x : C) : MulAut.conj (x : G) ∈ F := by
    rw [mem_fixingSubgroup_iff]
    intro y hy
    change (x : G) * y * (x : G)⁻¹ = y
    rw [← x.property y hy, mul_inv_cancel_right]
  let f : C → I := fun x => ⟨⟨MulAut.conj (x : G), hf x⟩, ⟨x, rfl⟩⟩
  have hs : Function.Surjective f := by
    intro a
    obtain ⟨x, hx⟩ := a.property
    change MulAut.conj x = (a.val : MulAut G) at hx
    have hc : x ∈ C := by
      intro y hy
      have he := (mem_fixingSubgroup_iff (MulAut G)).mp a.val.property y hy
      rw [← hx] at he
      change x * y * x⁻¹ = y at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    exact ⟨⟨x, hc⟩, Subtype.ext (Subtype.ext hx)⟩
  have hc : Nat.card I ≤ Nat.card C := Nat.card_le_card_of_surjective f hs
  have hi : I.index ≤ (innerSubgroup G).index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (innerSubgroup G).index_ne_zero_of_finite)
      (relIndex_dvd_index_of_normal (innerSubgroup G) F)
  calc
    Nat.card F = Nat.card I * I.index := I.card_mul_index.symm
    _ ≤ Nat.card C * (innerSubgroup G).index := Nat.mul_le_mul hc hi

end MulAut
