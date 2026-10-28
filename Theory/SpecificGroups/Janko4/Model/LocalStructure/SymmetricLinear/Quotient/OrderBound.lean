module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.Filtration
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage

/-!
# Local order divisibility from the full max4 diagonal action

The literal max4 subgroup has a certified faithful block-triangular action.
Its simultaneous diagonal kernel is a two-group. The kernel-index formula
therefore reduces the required odd-part bound to the order of the full
diagonal image. The certified commuting factors bound that image order by
divisibility into 120 * 168 = 20160, giving the unconditional theorem
`max4_card_dvd_twoPower_mul`.

A representation of the actual S5 × SL3(2) model whose image contains both
diagonal generators suffices. It need not be faithful or surjective onto the
whole matrix group, and no selected max4 epimorphism is used.

Source: Aschbacher--Smith, printed p.511/PDF p.528, and the literal ATLAS
program attributed in SymmetricLinear.Model. This supplies the order-divisibility
input to the separate two-core quotient comparison.
-/

public section
namespace Janko4.LocalStructure.SymmetricLinear

/-- The proved flag and two-group kernel reduce local order divisibility to
one finite simultaneous diagonal-image calculation. -/
theorem max4_card_dvd_twoPower_mul_of_diagonal_card
    (hc : Nat.card OrderBound.diagonalImage ∣ 20160) :
    ∃ n : ℕ, Nat.card max4Subgroup ∣ 2 ^ n * 20160 :=
  BinaryBlockOrder.card_dvd_twoPower_mul OrderBound.representation
    OrderBound.blockIndex OrderBound.representation_triangular
    OrderBound.representation_injective OrderBound.blockIndex_monotone hc

/-- The order of the literal ATLAS max4 subgroup divides a power of two times
20160. The full diagonal-image certificate discharges the finite-image premise,
independently of any selected epimorphism or quotient identification. -/
theorem max4_card_dvd_twoPower_mul :
    ∃ n : ℕ, Nat.card max4Subgroup ∣ 2 ^ n * 20160 :=
  max4_card_dvd_twoPower_mul_of_diagonal_card OrderBound.diagonalImage_card_dvd

private theorem quotientModel_card_for_order_bound : Nat.card QuotientModel = 20160 := by
  rw [Nat.card_prod, Atlas.Comparisons.Exceptional.sl3Two_card]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

/-- A concrete diagonal representation of the small product model also suffices
for the local order calculation. Its containment premises concern the literal
diagonal matrices, independently of any quotient map. -/
theorem max4_card_dvd_twoPower_mul_of_diagonal_cover
    (r : QuotientModel →* BinaryMatrixˣ)
    (hfirst : OrderBound.diagonalFirst ∈ r.range)
    (hsecond : OrderBound.diagonalSecond ∈ r.range) :
    ∃ n : ℕ, Nat.card max4Subgroup ∣ 2 ^ n * 20160 := by
  apply max4_card_dvd_twoPower_mul_of_diagonal_card
  rw [← quotientModel_card_for_order_bound]
  exact OrderBound.diagonalImage_card_dvd_of_cover r hfirst hsecond

end Janko4.LocalStructure.SymmetricLinear
