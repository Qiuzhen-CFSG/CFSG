module
public import Theory.GroupTheory.DoubleCoverCentralizer.Basic
public import Theory.GroupTheory.PGroup.ExponentFourRankOne
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Recognizing the small centralizer in a double cover

The centralizer has order four or eight. If every element outside the covering
center has order four, all involutions lie in its central subgroup of order two.
The exponent-four rank-one classification therefore gives C₄ or Q₈, with actual
isomorphisms to the standard models. No model name alone is used for recognition.

This is the elementary recognition step in the last paragraph of Aschbacher–Smith,
16.3.6, printed p.1179 / PDF p.1196 (1 March 2004 manuscript). The order and
lifting hypotheses are supplied by the separate action and covering arguments.
-/

@[expose] public section
namespace Theory.GroupTheory.DoubleCoverCentralizer
open Subgroup Theory.GroupTheory
variable {H : Type*} [Group H] [Finite H]

/-- A four- or eight-element subgroup of a double cover, with every element
outside the covering center of order four, is cyclic four or quaternion eight. -/
theorem centralizer_shape (C : Subgroup H) (hZC : center H ≤ C)
    (hZ : Nat.card (center H) = 2) (hC : Nat.card C = 4 ∨ Nat.card C = 8)
    (hfour : ∀ f : C, (f : H) ∉ center H → orderOf f = 4) :
    Nonempty (C ≃* QuaternionGroup 2) ∨
      (Nat.card C = 4 ∧ Nonempty (C ≃* Multiplicative (ZMod 4))) := by
  let Z := (center H).subgroupOf C
  have hZcard : Nat.card Z = 2 := (Nat.card_congr (subgroupOfEquivOfLe hZC).toEquiv).trans hZ
  have hz2 (z : C) (hz : z ∈ Z) : z ^ 2 = 1 := by
    have hp : (⟨z, hz⟩ : Z) ^ Nat.card Z = 1 := pow_card_eq_one'
    rw [hZcard] at hp
    exact congrArg Subtype.val hp
  have hp : IsPGroup 2 C := by
    rcases hC with hc | hc
    · exact IsPGroup.of_card (n := 2) hc
    · exact IsPGroup.of_card (n := 3) hc
  have hexp : ∀ f : C, f ^ 4 = 1 := by
    intro f
    by_cases hf : f ∈ Z
    · have hh := hz2 f hf
      calc
        f ^ 4 = (f ^ 2) ^ 2 := by rw [← pow_mul]
        _ = 1 := by rw [hh, one_pow]
    · simpa only [hfour f hf] using pow_orderOf_eq_one f
  have hno : ∀ B : Subgroup C, IsElementaryAbelian 2 B → Nat.card B ≠ 4 := by
    intro B hB hc
    let := hB
    have hBZ : B ≤ Z := by
      intro f hf
      by_contra hn
      have hf2 : f ^ 2 = 1 := congrArg Subtype.val
        (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 B) ⟨f, hf⟩)
      have hd := orderOf_dvd_of_pow_eq_one hf2
      rw [hfour f hn] at hd
      norm_num at hd
    have hh := card_le_of_le hBZ
    rw [hc, hZcard] at hh
    omega
  rcases hp.isCyclic_or_quaternion_two_of_no_elementary_four hexp hno with hcyc | hq
  · let := hcyc
    obtain ⟨f, hf⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp hcyc
    have hd : Nat.card C ∣ 4 := hf ▸ orderOf_dvd_of_pow_eq_one (hexp f)
    have hc4 : Nat.card C = 4 := by
      rcases hC with h | h
      · exact h
      · rw [h] at hd
        norm_num at hd
    exact Or.inr ⟨hc4, ⟨mulEquivOfCyclicCardEq (by
      simpa only [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] using hc4)⟩⟩
  · exact Or.inl hq

end Theory.GroupTheory.DoubleCoverCentralizer
