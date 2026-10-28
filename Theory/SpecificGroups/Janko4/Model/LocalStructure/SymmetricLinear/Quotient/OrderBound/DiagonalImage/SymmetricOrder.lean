module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.Factors
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.SymmetricOrder.Presentation

/-!
# The order of the concrete symmetric factor divides 120

The full-matrix type-A4 presentation cover contains both literal symmetric
factor generators. Lagrange's theorem and the homomorphism range order formula
therefore show that their actual subgroup closure has order dividing 5! = 120.
The multiplication homomorphism from the two commuting factors then bounds the
entire diagonal image by 120 times the order of the independent linear factor.

This discharges the symmetric-factor count in the max4 diagonal-image argument.
The independent linear-factor count, and the final 20160 bound, belong to the
parent assembly. Source: ATLAS J4G1-max4W1 and J4G1-f2r112B0 (attributed in
SymmetricLinear.Model and Model.Data); Aschbacher--Smith printed p.511/PDF p.528.
-/

public section
namespace Janko4.LocalStructure.SymmetricLinear.OrderBound.DiagonalFactors

/-- The actual full-matrix symmetric factor has order dividing 120. -/
theorem symmetricFactor_card_dvd : Nat.card symmetricFactor ∣ 120 := by
  have hle : symmetricFactor ≤ SymmetricOrder.permutationHom.range := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases hx with rfl | rfl
    · exact SymmetricOrder.symmetricFirst_mem_range
    · exact SymmetricOrder.symmetricSecond_mem_range
  have h := (Subgroup.card_dvd_of_le hle).trans
    (Subgroup.card_range_dvd SymmetricOrder.permutationHom)
  simpa only [Nat.card_perm, Nat.card_fin, Nat.factorial] using h

/-- Consumer for the literal diagonal generators and the certified factorHom.
The independent linear-factor order is deliberately retained without a premise. -/
theorem diagonalImage_card_dvd_symmetric_mul_linear :
    Nat.card OrderBound.diagonalImage ∣ 120 * Nat.card linearFactor := by
  have h := diagonalImage_card_dvd_of_cover factorHom
    diagonalFirst_mem_factorHom diagonalSecond_mem_factorHom
  rw [Nat.card_prod] at h
  exact h.trans (Nat.mul_dvd_mul symmetricFactor_card_dvd (dvd_refl _))

end Janko4.LocalStructure.SymmetricLinear.OrderBound.DiagonalFactors
