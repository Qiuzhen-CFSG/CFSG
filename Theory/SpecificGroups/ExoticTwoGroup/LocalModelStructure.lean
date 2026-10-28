module

public import Theory.SpecificGroups.ExoticTwoGroup.LocalModel
public import Theory.SpecificGroups.ExoticTwoGroup.LocalStructure
public import Theory.SpecificGroups.ExoticTwoGroup.LocalCentralizerPowers
public import Mathlib.GroupTheory.Index

/-!
# Local structure of the concrete exotic two-group

The outer coordinates identify the core and its index-two extension: the core
has trivial outer coordinate, and the even subgroup has trivial t coordinate.
The normal form proves both generation statements. Kernel-checked finite
certificates classify the remaining involutions by conjugating witnesses and
count the three involution centralizers. The characteristic lines are supplied
by the power calculations in LocalCentralizerPowers.

Source: Janko–Thompson, Math. Z. 113 (1970), 1.4(c), p.386 and p.396.
This module proves the local structure for the already constructed finite model;
transport to other presentations is handled separately.
-/

namespace ExoticTwoGroup.LocalModel

local instance : DecidableEq Model := inferInstance

/-- The core consists precisely of elements with trivial outer coordinate. -/
public theorem mem_core_iff (x : Model) : x ∈ presentation.core ↔ x.right = 1 := by
  constructor
  · intro hx
    have h : presentation.core ≤ (SemidirectProduct.rightHom : Model →* Actor).ker := by
      apply (Subgroup.closure_le _).mpr
      intro y hy
      change y ∈ ({a, b, g₁, g₂} : Set Model) at hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl <;> rfl
    exact h hx
  · intro hx
    have hn := normal_form x
    simp only [hx, Prod.fst_one, Prod.snd_one, toAdd_one,
      ZMod.val_zero, pow_zero, mul_one] at hn
    rw [hn]
    repeat' apply Subgroup.mul_mem
    all_goals
      apply Subgroup.pow_mem
      exact Subgroup.subset_closure (by simp [presentation])

/-- The even subgroup consists precisely of elements with trivial t coordinate. -/
public theorem mem_even_iff (x : Model) : x ∈ presentation.evenSubgroup ↔ x.right.1 = 1 := by
  constructor
  · intro hx
    have h : presentation.evenSubgroup ≤
        ((MonoidHom.fst C2 C2).comp (SemidirectProduct.rightHom : Model →* Actor)).ker := by
      apply (Subgroup.closure_le _).mpr
      intro y hy
      change y ∈ ({a, b, g₁, g₂, z₀} : Set Model) at hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl <;> rfl
    exact h hx
  · intro hx
    have hn := normal_form x
    simp only [hx, toAdd_one, ZMod.val_zero, pow_zero, mul_one] at hn
    rw [hn]
    repeat' apply Subgroup.mul_mem
    all_goals
      apply Subgroup.pow_mem
      exact Subgroup.subset_closure (by simp [presentation])

private theorem central_order : orderOf (a^2*b^2) = 2 :=
  orderOf_eq_prime (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem central_mem : a^2*b^2 ∈ Subgroup.center Model := by
  rw [Subgroup.mem_center_iff]
  decide +kernel

private theorem t_order : orderOf t = 2 :=
  orderOf_eq_prime (by decide +kernel) (by decide +kernel)

private theorem z₀_order : orderOf z₀ = 2 :=
  orderOf_eq_prime (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem even_eq_centralizer :
    presentation.evenSubgroup = Subgroup.centralizer (presentation.four : Set Model) := by
  change presentation.evenSubgroup = Subgroup.centralizer
    (Subgroup.closure ({a^2, b^2} : Set Model) : Set Model)
  rw [Subgroup.centralizer_closure]
  ext x
  rw [mem_even_iff, Subgroup.mem_centralizer_iff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  exact (by decide +kernel : ∀ y : Model,
    y.right.1 = 1 ↔ a^2*y=y*a^2 ∧ b^2*y=y*b^2) x

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- The even subgroup has order 128. -/
public theorem card_even : Nat.card presentation.evenSubgroup = 128 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight mem_even_iff)]
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem even_index : presentation.evenSubgroup.index = 2 := by
  have h := presentation.evenSubgroup.index_mul_card
  rw [card_even, card_model] at h
  omega

-- Use square-one equations in the certificates, avoiding noncomputable orderOf.
-- The existential witnesses certify conjugacy by c*x = representative*c.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem even_conjugating_witnesses : ∀ x : Model, x^2=1 → x.right.1=1 →
    x.right=1 ∨ ∃ c : Model, c*x=z₀*c := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem odd_conjugating_witnesses : ∀ x : Model, x^2=1 → x.right.1≠1 →
    (∃ c : Model, c*x=t*c) ∨ (∃ c : Model, c*x=(t*z₀)*c) := by decide +kernel

private theorem isConj_of_witness {x y : Model} (h : ∃ c : Model, c*x=y*c) :
    IsConj x y := by
  obtain ⟨c, hc⟩ := h
  exact isConj_iff.mpr ⟨c, by rw [hc, mul_inv_cancel_right]⟩

private theorem even_classes (x : Model) (hx : orderOf x = 2)
    (he : x ∈ presentation.evenSubgroup) : x ∈ presentation.core ∨ IsConj x z₀ := by
  obtain hc | hz := even_conjugating_witnesses x
    (orderOf_eq_prime_iff.mp hx).1 ((mem_even_iff x).mp he)
  · exact Or.inl ((mem_core_iff x).mpr hc)
  · exact Or.inr (isConj_of_witness hz)

private theorem odd_classes (x : Model) (hx : orderOf x = 2)
    (he : x ∉ presentation.evenSubgroup) : IsConj x t ∨ IsConj x (t*z₀) := by
  have ho : x.right.1 ≠ 1 := fun h => he ((mem_even_iff x).mpr h)
  obtain ht | hz := odd_conjugating_witnesses x (orderOf_eq_prime_iff.mp hx).1 ho
  · exact Or.inl (isConj_of_witness ht)
  · exact Or.inr (isConj_of_witness hz)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- The centralizer of t has order 32. -/
public theorem t_centralizer_card :
    Nat.card (Subgroup.centralizer ({t} : Set Model)) = 32 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight
    (fun x : Model => Subgroup.mem_centralizer_singleton_iff))]
  rw [Nat.card_eq_fintype_card]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- The centralizer of tz₀ has order 32. -/
public theorem tz₀_centralizer_card :
    Nat.card (Subgroup.centralizer ({t*z₀} : Set Model)) = 32 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight
    (fun x : Model => Subgroup.mem_centralizer_singleton_iff))]
  rw [Nat.card_eq_fintype_card]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- The centralizer of z₀ has order 16. -/
public theorem z₀_centralizer_card :
    Nat.card (Subgroup.centralizer ({z₀} : Set Model)) = 16 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight
    (fun x : Model => Subgroup.mem_centralizer_singleton_iff))]
  rw [Nat.card_eq_fintype_card]
  decide +kernel

/-- The concrete exotic group satisfies the full local-structure interface. -/
public theorem localStructure : presentation.LocalStructure where
  central_order := central_order
  central_mem := central_mem
  t_order := t_order
  z₀_order := z₀_order
  even_index := even_index
  even_eq_centralizer := even_eq_centralizer
  even_classes := even_classes
  odd_classes := odd_classes
  t_not_even := by
    rw [mem_even_iff]
    decide
  z₀_mem_even := (mem_even_iff z₀).mpr rfl
  t_centralizer_card := t_centralizer_card
  tz₀_centralizer_card := tz₀_centralizer_card
  z₀_centralizer_card := z₀_centralizer_card
  characteristic_line := characteristic_line

end ExoticTwoGroup.LocalModel
