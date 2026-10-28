module
public import Theory.SpecificGroups.Rudvalis.Model.LocalStructure.BinaryThreeModules.Normalizer
public import Theory.GroupTheory.NormalizerTransitivity
public import Theory.SpecificGroups.Rudvalis.Model.LocalStructure.BinaryThreeModules.RowConjugacy

/-!
# Transitive normalizers of elementary order-64 subgroups in Rudvalis

Every elementary subgroup of order sixty-four is conjugate to one of four
certified Sylow rows.  Explicit Sylow generators carry each row to the first
one, whose two certified normalizing words act transitively on its 63
nonidentity elements.  Transporting that action back gives the result for the
original subgroup, with no Sylow-normality or odd-index assumption.

Source: GLS3 Table 5.3r, p.279, and the native local inspection used in
Aschbacher--Smith 4.4.3, pp.622--623.  The finite facts are checked in the
imported row and normalizer certificates.
-/

public noncomputable section
namespace Rudvalis.BinaryThreeModules.ElementarySixtyFour
open Subgroup

/-- Every native elementary subgroup of order sixty-four has a normalizer
transitive on its nonidentity elements. -/
theorem normalizer_transitive
    (W : Subgroup Model) [IsElementaryAbelian 2 W] (hcard : Nat.card W = 64) :
    ∀ x y : W, x ≠ 1 → y ≠ 1 →
      ∃ p : normalizer (W : Set Model), p.val * x.val * p.val⁻¹ = y.val := by
  obtain ⟨g,j,hj⟩ := exists_conjugate_row W hcard
  obtain ⟨k,hk⟩ := exists_row_conjugate_zero j
  have hcj : Nat.card (row j) = 64 := by
    rw [←hj, card_map_of_injective (MulAut.conj g).injective, hcard]
  have hc0 : Nat.card (row 0) = 64 := by
    rw [←hk, card_map_of_injective (MulAut.conj k).injective, hcj]
  exact normalizer_transitive_of_equiv (MulAut.conj g) W (row j) hj
    (normalizer_transitive_of_equiv (MulAut.conj k) (row j) (row 0) hk
      (row0_transitive_of_card hc0))

end Rudvalis.BinaryThreeModules.ElementarySixtyFour
