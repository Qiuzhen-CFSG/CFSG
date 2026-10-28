module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.Filtration
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.Factors
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.LinearOrder
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.SymmetricOrder

/-!
# Counting the full max4 diagonal image by its commuting factors

The actual simultaneous diagonal generators lie in the homomorphic image of
the product of two explicitly certified commuting matrix groups. Divisibility
by 20160 follows from their proved order bounds: the symmetric factor is covered
by a representation of S₅, and the linear factor has a checked enumeration of
168 full matrices. The resulting bound concerns all fifteen diagonal blocks
simultaneously and has no additional premises.

Source: ATLAS J4G1-max4W1, J4G1-f2r112B0, and Aschbacher--Smith printed
p.511/PDF p.528. See DiagonalImage/source/README.md.
-/

public section
namespace Janko4.LocalStructure.SymmetricLinear.OrderBound
open DiagonalFactors

/-- Full-matrix factorization reduces the simultaneous diagonal-image bound
to two independent finite subgroup counts. -/
theorem diagonalImage_card_dvd_of_factor_cards
    (hs : Nat.card symmetricFactor ∣ 120)
    (hl : Nat.card linearFactor ∣ 168) : Nat.card diagonalImage ∣ 20160 := by
  have h := diagonalImage_card_dvd_of_cover factorHom
    diagonalFirst_mem_factorHom diagonalSecond_mem_factorHom
  rw [Nat.card_prod] at h
  exact h.trans (show Nat.card symmetricFactor * Nat.card linearFactor ∣ 20160 from
    Nat.mul_dvd_mul hs hl)

/-- The full simultaneous diagonal image of the literal max4 subgroup has order
dividing 20160. This discharges the finite-image premise of the local order bound. -/
theorem diagonalImage_card_dvd : Nat.card diagonalImage ∣ 20160 :=
  diagonalImage_card_dvd_of_factor_cards symmetricFactor_card_dvd linearFactor_card_dvd

end Janko4.LocalStructure.SymmetricLinear.OrderBound
