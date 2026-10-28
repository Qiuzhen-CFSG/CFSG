module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.TwoPrimary.BinaryModel.Order

/-!
# An index-four binary pair in the full PSU₄(3) involution centralizer

The map `pair` is obtained from the two determinant-one unitary coordinate
blocks and the literal SU₄-to-PSU₄ projection. Its image is normal in the
full projective centralizer, its kernel is the diagonal central sign of
order two, and its image has index four. The order calculation includes
block interchange and the complete scalar kernel of order four.

This is the concrete model input for the independent central-extension
calculation in the two-primary multiplier bound. It assumes no multiplier
statement. Source: Aschbacher–Smith I.1.4(5), printed p.408 of
`refs/quasithin.pdf`; GLS3, chapter 6, §6.1.
-/

public section
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal
open GLS3.Chapter5.SchurPresentation
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.TwoPrimary.BinaryModel

/-- One actual block map has all three required local-model properties. -/
theorem exists_binary_pair :
    ∃ j : (BinaryTetrahedral × BinaryTetrahedral) →* standardCentralizer,
      j.range.Normal ∧ Nat.card j.ker = 2 ∧ j.range.index = 4 :=
  ⟨pair, pair_range_normal, pair_kernel_card, pair_range_index⟩

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.TwoPrimary.BinaryModel
