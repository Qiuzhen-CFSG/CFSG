module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Index

/-!
# Cubic commutators from a nonnormal four-subgroup of S₄

The even involutions form the normal Klein four-group. An elementary
four-subgroup that is not normal consequently contains an odd involution,
which has an order-three commutator with a suitable permutation. The proof
checks only the small permutation identities on four letters. We also
verify the trivial center needed when reselecting an outer involution.

The actual fixed-group application is `cubic_witness_of_nonnormal_four` in
`EightCentralizers.Reselection`; it retains the action expression used by
the source consumer rather than merely identifying an abstract S₄.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 4.2,
manuscript p.10.
-/

public section

namespace Matrix.PSL3Three.GraphWitnesses.EightCentralizers
open Subgroup
private abbrev P := Equiv.Perm (Fin 4)

private theorem even_involution_product : ∀ x y : P,
    x ^ 2 = 1 → Equiv.Perm.sign x = 1 →
    y ^ 2 = 1 → Equiv.Perm.sign y = 1 → (x * y) ^ 2 = 1 := by
  decide +kernel

private def evenInvolutions : Subgroup P where
  carrier := {x | x ^ 2 = 1 ∧ Equiv.Perm.sign x = 1}
  one_mem' := by simp
  mul_mem' hx hy := ⟨even_involution_product _ _ hx.1 hx.2 hy.1 hy.2,
    by simp only [map_mul, hx.2, hy.2, mul_one]⟩
  inv_mem' hx := ⟨by rw [inv_pow, hx.1, inv_one], by rw [map_inv, hx.2, inv_one]⟩

private instance : evenInvolutions.Normal where
  conj_mem x hx g := by
    constructor
    · change (MulAut.conj g x) ^ 2 = 1
      rw [← map_pow, hx.1, map_one]
    · change Equiv.Perm.sign (g * x * g⁻¹) = 1
      rw [map_mul, map_mul, map_inv, hx.2, mul_one, mul_inv_cancel]

private theorem card_evenInvolutions : Nat.card evenInvolutions = 4 := by
  change Nat.card {x : P // x ^ 2 = 1 ∧ Equiv.Perm.sign x = 1} = 4
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem odd_involution_cubic : ∀ x : P, x ^ 2 = 1 → Equiv.Perm.sign x ≠ 1 →
    ∃ y : P, (x * y * x⁻¹ * y⁻¹) ^ 3 = 1 ∧ x * y * x⁻¹ * y⁻¹ ≠ 1 := by
  decide +kernel

theorem symmetricFour_four_cubic (D : Subgroup (Equiv.Perm (Fin 4)))
    (hD : IsElementaryAbelian 2 D) (hc : Nat.card D = 4) (hn : ¬ D.Normal) :
    ∃ x ∈ D, ∃ y : Equiv.Perm (Fin 4), orderOf (x * y * x⁻¹ * y⁻¹) = 3 := by
  let : IsElementaryAbelian 2 D := hD
  have hex : ∃ x ∈ D, Equiv.Perm.sign x ≠ 1 := by
    by_contra! h
    have hle : D ≤ evenInvolutions := fun x hx =>
      ⟨elemPow_eq_one_of_isElementaryAbelian x hx, h x hx⟩
    have he : D = evenInvolutions := Subgroup.eq_of_le_of_card_ge hle (by
      rw [hc, card_evenInvolutions])
    exact hn (he ▸ inferInstance)
  obtain ⟨x, hx, hs⟩ := hex
  obtain ⟨y, hy, hy1⟩ := odd_involution_cubic x
    (elemPow_eq_one_of_isElementaryAbelian x hx) hs
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact ⟨x, hx, y, orderOf_eq_prime hy hy1⟩

theorem symmetricFour_center_eq_bot : center (Equiv.Perm (Fin 4)) = ⊥ := by
  have hc : ∀ x : P, (∀ y : P, y * x = x * y) → x = 1 := by decide +kernel
  apply eq_bot_iff.mpr
  intro x hx
  exact hc x (mem_center_iff.mp hx)

end Matrix.PSL3Three.GraphWitnesses.EightCentralizers
