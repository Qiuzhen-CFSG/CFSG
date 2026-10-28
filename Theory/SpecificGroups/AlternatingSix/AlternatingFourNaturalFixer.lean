module
public import Theory.SpecificGroups.AlternatingSix.AlternatingFourActions
public import Theory.SpecificGroups.AlternatingSix.AlternatingFourFixer
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Natural pointwise fixers of an A₄ in A₆

The full pointwise fixer is a two-group. Its intersection with the inner
A₆ has no involution, since an A₆ involution has fixed group of order
eight and cannot fix an A₄. The natural fixer therefore injects into
S₆/A₆ and has order at most two.

This supplies the literal centralizer index in Aschbacher–Smith 2.4.36,
printed p.549 of the combined manuscript, 1 March 2004.
-/

@[expose] public section
open Subgroup
namespace AlternatingSix
open ShadowLocal

/-- Among natural automorphisms, the pointwise fixer of an actual A₄ has
order at most two. No choice of an A₄ conjugacy class is needed. -/
theorem alternatingFour_natural_fixer_card_le_two
    (L : Subgroup A6) (eL : L ≃* alternatingGroup (Fin 4))
    (A : Subgroup AutA6) (hA : A ≤ natural)
    (hf : ∀ a ∈ A, ∀ l ∈ L, a l = l) : Nat.card A ≤ 2 := by
  have hfix : A ≤ fixingSubgroup AutA6 (L : Set A6) := by
    intro a ha
    exact (mem_fixingSubgroup_iff _).mpr (hf a ha)
  let D := A ⊓ ShadowLocal.inner
  have hp : IsPGroup 2 D := (alternatingFour_fixer_isPGroup L eL).to_le
    (inf_le_left.trans hfix)
  have hD : D = ⊥ := by
    by_contra hne
    obtain ⟨a, ha, hane⟩ := D.bot_or_exists_ne_one.resolve_left hne
    let z : D := ⟨a ^ (orderOf a / 2), D.pow_mem ha _⟩
    have hz : orderOf z = 2 := by
      rw [← Subgroup.orderOf_coe]
      apply orderOf_pow_orderOf_div (Nat.ne_of_gt (orderOf_pos a))
      have hane' : (⟨a, ha⟩ : D) ≠ 1 := fun he => hane (congrArg Subtype.val he)
      change 2 ∣ orderOf (D.subtype ⟨a, ha⟩)
      rw [orderOf_injective D.subtype D.subtype_injective]
      exact hp.dvd_orderOf hane'
    have hzA : orderOf (z : AutA6) = 2 := by simpa only [Subgroup.orderOf_coe] using hz
    exact (alternatingFour_fixed_involution_natural_outer L eL z hzA
      (hf z z.property.1)).2 z.property.2
  have hd : Disjoint ShadowLocal.inner A := by
    rw [disjoint_iff, inf_comm]
    exact hD
  have hc := card_sup_eq_mul_of_normalizes_of_disjoint ShadowLocal.inner A
    le_normalizer_of_normal hd
  have hb := card_le_of_le (show ShadowLocal.inner ⊔ A ≤ natural from
    sup_le inner_le_natural hA)
  rw [hc, card_inner, card_natural] at hb
  omega

end AlternatingSix
