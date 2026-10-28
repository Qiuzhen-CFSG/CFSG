module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.Data.ZMod.Basic

/-!
# The outer A6–C3 group configuration

This source-level record retains the literal commuting factors and conjugation
by the outer generator in B.5.6(4). It makes no assertion about a direct sum
with the ambient fixed space. The rank-five obstruction is therefore separate
from the group configuration consumed by later exclusions.

Source: Aschbacher–Smith, B.5.6(4) and B.5.7, printed pp.105–106.
Constructing this configuration from B.5.3 remains a classification theorem.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterB

structure OuterSixThreeShape (D : Type*) [Group D] where
  first : Subgroup D
  second : Subgroup D
  product : (first × second) ≃* ↥(first ⊔ second)
  product_apply : ∀ a b, (product (a, b) : D) = (a : D) * (b : D)
  firstEquiv : first ≃* alternatingGroup (Fin 6)
  secondEquiv : second ≃* Multiplicative (ZMod 3)
  element : D
  generates : (first ⊔ second) ⊔ zpowers element = ⊤
  firstOuter : ∃ α : MulAut first,
    (∀ a : first, (α a : D) = element * (a : D) * element⁻¹) ∧
      α ∉ (MulAut.conj (G := first)).range
  secondOuter : ∃ α : MulAut second,
    (∀ a : second, (α a : D) = element * (a : D) * element⁻¹) ∧
      α ∉ (MulAut.conj (G := second)).range

theorem OuterSixThreeShape.card_ge {D : Type*} [Group D] [Finite D]
    (h : OuterSixThreeShape D) : 360 ≤ Nat.card D := by
  have he : Nat.card h.first = 360 := by
    rw [Nat.card_congr h.firstEquiv.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  exact he ▸ Nat.card_le_card_of_injective h.first.subtype h.first.subtype_injective

end CFSG.Quasithin.ChapterB
