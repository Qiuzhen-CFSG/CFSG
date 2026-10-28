module
public import Theory.ElementaryAbelian.Basic
public import Mathlib.Algebra.Group.Conj
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Data.Fintype.Card
/-!
# Counting a half-space involution fusion class

Suppose every involution in a distinguished subgroup A is conjugate to z,
and every involution in H outside A is conjugate to t, where t and z are
not conjugate. In an elementary sixteen Q inside H with |Q ∩ A| = 8,
exactly eight elements are conjugate to t.

The proof identifies the fusion class in Q with the complement of Q ∩ A
and subtracts the two subgroup cardinalities. The ambient conjugacy is kept
literal. Source: Aschbacher--Smith, Lemma 2.5.15, printed p.559.
-/
public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The distinguished involution class occupies exactly half the elementary sixteen. -/
theorem central_involution_fusion_card
    (H A Q : Subgroup G) (t z : G) (ht : orderOf t = 2)
    (hQ : IsElementaryAbelian 2 Q) (hQH : Q ≤ H)
    (hQc : Nat.card Q = 16) (hAc : Nat.card (Q ⊓ A : Subgroup G) = 8)
    (hnf : ¬ IsConj t z)
    (hinside : ∀ a ∈ A, orderOf a = 2 → IsConj z a)
    (houtside : ∀ a ∈ H, a ∉ A → orderOf a = 2 → IsConj t a) :
    Nat.card {x : G // x ∈ Q ∧ IsConj t x} = 8 := by
  classical
  let : Fintype Q := Fintype.ofFinite Q
  let : IsElementaryAbelian 2 Q := hQ
  have htne : t ≠ 1 := by intro he; simp [he] at ht
  have hxiff (x : Q) : IsConj t (x : G) ↔ (x : G) ∉ A := by
    constructor
    · intro hc hxA
      have hxne : (x : G) ≠ 1 := fun he => htne (isConj_one_left.mp (he ▸ hc))
      have hxo : orderOf (x : G) = 2 :=
        orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian _ x.property) hxne
      exact hnf (hc.trans (hinside x hxA hxo).symm)
    · intro hxA
      have hxne : (x : G) ≠ 1 := fun he => hxA (he ▸ A.one_mem)
      exact houtside x (hQH x.property) hxA
        (orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian _ x.property) hxne)
  let d : {x : G // x ∈ Q ∧ IsConj t x} ≃ {x : Q // (x : G) ∉ A} :=
    { toFun x := ⟨⟨x.val,x.property.1⟩, (hxiff ⟨x.val,x.property.1⟩).mp x.property.2⟩
      invFun x := ⟨x.val.val,x.val.property,(hxiff x.val).mpr x.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  let dA : {x : Q // (x : G) ∈ A} ≃ (Q ⊓ A : Subgroup G) :=
    { toFun x := ⟨x.val.val,x.val.property,x.property⟩
      invFun x := ⟨⟨x.val,x.property.1⟩,x.property.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  have hcA : Fintype.card {x : Q // (x : G) ∈ A} = 8 := by
    rw [← Nat.card_eq_fintype_card,Nat.card_congr dA,hAc]
  rw [Nat.card_congr d,Nat.card_eq_fintype_card,Fintype.card_subtype_compl,hcA,
    ← Nat.card_eq_fintype_card,hQc]
end Subgroup
