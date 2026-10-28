module

public import Theory.GroupTheory.PCoreProduct
public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
public import Mathlib.GroupTheory.RegularWreathProduct
public import Mathlib.Data.ZMod.Basic

/-!
# The two-core and center of a pair of alternating four-groups

The unique Sylow two-subgroup of `A₄` is its characteristic Klein four-group.
Prime cores commute with direct products, so `O₂(A₄ × A₄)` has order sixteen;
the product is centerless. We also record the order of the literal symmetric
wreath product used to recognize its full automorphism group.

These intrinsic facts support the recognition argument in Aschbacher–Smith,
Lemma 15.3.9, printed p.1123 (combined manuscript, 1 March 2004).
The automorphism-group identification is not asserted here.
-/

@[expose] public section
open Subgroup
namespace AlternatingFourPair
abbrev A := alternatingGroup (Fin 4)
abbrev Model := A × A

/-- The two-core of `A₄` is its unique Sylow two-subgroup. -/
theorem twoCore_eq_kleinFour : pCore 2 A = alternatingGroup.kleinFour (Fin 4) := by
  have hcard : Nat.card (alternatingGroup.kleinFour (Fin 4)) = 4 :=
    alternatingGroup.kleinFour_card_of_card_eq_four (by norm_num)
  apply le_antisymm
  · obtain ⟨S, hS⟩ := (pCore_isPGroup (p := 2) (G := A)).exists_le_sylow
    rw [alternatingGroup.two_sylow_eq_kleinFour_of_card_eq_four (by norm_num) S] at hS
    exact hS
  · exact le_sSup ⟨alternatingGroup.normal_kleinFour (by norm_num),
      IsPGroup.of_card (n := 2) (by simpa using hcard)⟩

/-- The two-core of the direct product has order sixteen. -/
theorem card_twoCore : Nat.card (pCore 2 Model) = 16 := by
  rw [pCore_prod, twoCore_eq_kleinFour]
  rw [Nat.card_congr (prodEquiv _ _).toEquiv, Nat.card_prod]
  rw [alternatingGroup.kleinFour_card_of_card_eq_four (by norm_num)]

/-- The direct product has trivial center. -/
theorem center_eq_bot : center Model = ⊥ := by
  rw [Subgroup.center_prod, alternatingGroup.center_eq_bot (by norm_num : 4 ≤ Nat.card (Fin 4))]
  exact bot_prod_bot

/-- The target is the literal regular wreath product, of order 1152. -/
theorem symmetric_wreath_card :
    Nat.card (RegularWreathProduct (Equiv.Perm (Fin 4)) (Multiplicative (ZMod 2))) = 1152 := by
  rw [RegularWreathProduct.card]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

end AlternatingFourPair

end
