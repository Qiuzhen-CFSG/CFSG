module

public import Theory.SpecificGroups.Rudvalis.Model.FivePointBase

/-!
# Two finite witnesses for Rudvalis displacement

The first standard involution has no fixed point in the actual degree-4060
action. The commutator with one short word has order 29. These facts allow
involution-class separation and a binary moved-dimension bound without a
classification of small representations. The order identity is checked on
the certified five-point base, rather than on all 4060 letters.

Source: the native ATLAS permutations and conventions in `PermutationData`;
GLS III, Table 5.3r, and the Rudvalis argument in Guralnick--Malle,
*Classification of 2F-modules I*, Proposition 5.1. The conjugator was found
by a bounded word search; the identities below are kernel checked.
-/

public section
namespace Rudvalis.DirectDisplacementWords

/-- The short conjugator producing an order-29 product of 2B involutions. -/
@[expose] def conjugator : Model := b * a * b * a * b⁻¹

/-- The product of the two actual conjugate involutions. -/
@[expose] def oddWord : Model := a * (conjugator⁻¹ * a * conjugator)

set_option maxRecDepth 6000 in
/-- The actual first ATLAS involution fixes none of the 4060 letters. -/
theorem a_no_fixed_point : ∀ i : Fin 4060, a • i ≠ i := by
  decide +kernel

set_option maxRecDepth 3000 in
/-- The word's 29th power is certified on the existing five-point base. -/
theorem oddWord_pow : oddWord ^ 29 = 1 := by
  apply eq_of_smul_first_five
  decide +kernel

/-- The word is nontrivial on the distinguished point. -/
theorem oddWord_ne_one : oddWord ≠ 1 := by
  have hn : oddWord • (0 : Fin 4060) ≠ (0 : Fin 4060) := by decide +kernel
  intro he
  exact hn (by rw [he, one_smul])

/-- The precise prime order needed by the displacement argument. -/
theorem oddWord_order : orderOf oddWord = 29 := by
  let : Fact (Nat.Prime 29) := ⟨by decide⟩
  exact orderOf_eq_prime oddWord_pow oddWord_ne_one

/-- The product is the commutator used by the generic rank inequality. -/
theorem oddWord_eq_commutator :
    oddWord = a * conjugator⁻¹ * a⁻¹ * (conjugator⁻¹)⁻¹ := by
  have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using a_sq)
  simp only [oddWord, ha, inv_inv, mul_assoc]

end Rudvalis.DirectDisplacementWords
