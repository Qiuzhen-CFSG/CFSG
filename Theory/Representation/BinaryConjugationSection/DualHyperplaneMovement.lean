module
public import Theory.Representation.BinaryConjugationSection.DualHyperplanes

/-!
# Movement on a denominator meeting two dual supports

An index-two denominator meets each support in a hyperplane modulo the
common kernel. A faithful actor of rank at least two cannot fix both: the
displacement embedding bounds its rank by the product of the two fixed
codimensions. Thus one literal denominator/support intersection is moved.

Source: Aschbacher--Smith, 14.6.24(4), final paragraph, printed p.1041.
-/

public section
open Subgroup Representation.BinaryOffender

namespace Representation.BinaryConjugationSection
variable {G X V : Type*} [Group G] [Finite G] [Group X] [Finite X]
  [AddCommGroup V] [Module (ZMod 2) V]

theorem moves_one_of_dual_hyperplanes
    (H U Z A D W Wdual : Subgroup G)
    (σ : Representation (ZMod 2) X V) (hσ : Function.Injective σ) (π : H →* X)
    (c : BinaryConjugationSection H W Z (σ.comp π))
    (cdual : BinaryConjugationSection H Wdual Z (σ.dual.comp π))
    (hWU : W ≤ U) (hWdualU : Wdual ≤ U) (hZD : Z ≤ D)
    (hindex : D.relIndex U ≤ 2) (hrank : 2 ≤ rank ((A.subgroupOf H).map π)) :
    ¬ A ≤ centralizer ((D ⊓ W : Subgroup G) : Set G) ∨
      ¬ A ≤ centralizer ((D ⊓ Wdual : Subgroup G) : Set G) := by
  let : Finite V := Finite.of_surjective (fun w : W => (c.coordinates w).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  by_contra hn
  push Not at hn
  have hi (S : Subgroup G) (hS : S ≤ U) : (D ⊓ S).relIndex S ≤ 2 := by
    rw [inf_relIndex_right]
    exact (relIndex_le_of_le_right hS
      (show D.relIndex U ≠ 0 from (D.subgroupOf U).index_ne_zero_of_finite)).trans hindex
  have hc : ⁅A,D ⊓ W⁆ ≤ Z := (commutator_eq_bot_iff_le_centralizer.mpr hn.1).le.trans bot_le
  have hc' : ⁅A,D ⊓ Wdual⁆ ≤ Z := (commutator_eq_bot_iff_le_centralizer.mpr hn.2).le.trans bot_le
  have h₁ := fixedCodim_le_one_of_fixed_index H W Z A (D ⊓ W) σ π c
    inf_le_right (le_inf hZD c.kernel_le) hc (hi W hWU)
  have h₂ := fixedCodim_le_one_of_fixed_index H Wdual Z A (D ⊓ Wdual) σ.dual π cdual
    inf_le_right (le_inf hZD cdual.kernel_le) hc' (hi Wdual hWdualU)
  have hb := rank_le_fixedCodim_mul_dual σ hσ ((A.subgroupOf H).map π)
  have hm := Nat.mul_le_mul h₁ h₂
  omega
end Representation.BinaryConjugationSection
