module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.LinearProjection.Descent
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.LinearProjection.Generation
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.LinearProjection.LeviProduct
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.LinearProjection.SplitRetraction

/-!
# The binary Ree linear projection

The split linear seed retracts onto its actual end-node Levi, with exactly
the root radical as kernel. The concrete identification of this Levi with
SL₂(2) × SL₂(2) carries the Ree twist to factor exchange. Restricting the
retraction to fixed points and identifying the diagonal with PSL₂(2) gives
the unconditional binary projection. The fixed Levi section proves its
surjectivity, and restriction of the split kernel gives the specified radical
inside the fixed seed.

Source: Aschbacher–Smith F.1.12(I)(5), printed pp.263–264 of
`refs/quasithin.pdf`. The ambient group is the full `ReeF4.Model 0`.
-/

public section
noncomputable section

namespace ReeF4.Parabolics.BinaryLinear

/-- The binary linear seed projects onto the actual projective matrix group PSL₂(2). -/
def projection : seed 0 .linear →* LargeLocalSeeds.LinearQuotient 0 :=
  projectionOfSplitData splitRetraction splitRetraction_twist
    leviProductEquiv leviProductEquiv_twist

/-- The fixed end-node Levi supplies a preimage of every projective matrix. -/
theorem projection_surjective : Function.Surjective projection :=
  projectionOfSplitData_surjective splitRetraction splitRetraction_twist
    splitRetraction_levi leviProductEquiv leviProductEquiv_twist

/-- The kernel is exactly the existing root radical relative to the binary seed. -/
theorem projection_ker : projection.ker = radicalInSeed 0 .linear :=
  projectionOfSplitData_ker splitRetraction splitRetraction_twist
    splitRetraction_ker leviProductEquiv leviProductEquiv_twist

end ReeF4.Parabolics.BinaryLinear
