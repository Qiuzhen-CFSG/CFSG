module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.FixedCoordinates.Blocks
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.FixedCoordinates.MatrixRelations.IntegralB2
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.FixedCoordinates.MatrixRelations.Exponential
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.FixedCoordinates.MatrixRelations.SignedBrackets

/-!
# Actual matrix relations for the Ree fixed-coordinate blocks

Mixed-length roots with nonnegative inner product commute in the integral
Chevalley representation, so they commute over every Ree coefficient field,
including the binary field at m = 0. The proof uses absent root weights and
integral factorial cancellation; it does not use the Ree group order.

For a positive B₂ block, the two signed integral brackets and the four zero
brackets from geometry give the finite-exponential swap. Specializing that
integral identity to the coefficient field removes the signs and gives the
exact correction parameters `a * b` and `a * b ^ 2`. Lifting the root-curve
equality to the split group proves the block relation for every parameter.

Source: the root calculation underlying Aschbacher–Smith F.1.12(I)(5),
`refs/quasithin.pdf`, printed p.263 (PDF p.274).
-/

public section

namespace ReeF4.Parabolics.RadicalCoordinates.FixedCoordinates

/-- Actual mixed-length root generators commute, for every Ree parameter. -/
theorem mixedRootCommutation (m : ℕ) : MixedRootCommutation m := by
  intro r s hr hs hl hshort hd a b
  obtain ⟨h0, hsum⟩ := MatrixRelations.mixed_sum_absent r s hl hshort hd
  change rootGeneratorInGroup m r a * rootGeneratorInGroup m s b =
    rootGeneratorInGroup m s b * rootGeneratorInGroup m r a
  apply Subtype.ext
  exact (MatrixRelations.rootCurves_commute_of_operators_commute r s
    (MatrixRelations.positive_operators_commute r s hr hs h0 hsum) a b).eq

/-- The exact B₂ swap for actual root generators, including the binary field.
All integral bracket premises are discharged from the stated root geometry. -/
theorem b2RootSwap (m : ℕ) : B2RootSwap m := by
  intro r s c d hr hs hl hshort hdot hc hd a b
  apply Subtype.ext
  exact MatrixRelations.rootCurve_swap_of_integralB2 m r s c d
    (MatrixRelations.integralB2Relations_of_brackets r s c d hr hs hl hshort hdot hc hd
      (MatrixRelations.b2BracketRelations r s c d hr hs hl hshort hdot hc hd)) a b

end ReeF4.Parabolics.RadicalCoordinates.FixedCoordinates
