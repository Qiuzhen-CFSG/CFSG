module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.TorusPlacement.ScalarShape.Operators
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.TorusPlacement.ScalarShape.FixedRows
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.TorusPlacement.ScalarShape.Diagonalization.Support

/-!
# Diagonalization reductions for central evaluated E6 words

`Support` combines the integral complementary gradings preserved by actual
six-node words with their six Cartan commutator equations. Every nonzero matrix
entry has equal integral grades and equal Cartan weights in the coefficient
field. The original Cartan commutator exports remain re-exported here.

Final diagonality still requires root-coordinate separation within these
classes and elimination of the off-diagonal Cartan entries, particularly in
characteristic three. The reductions live below this assembly module so that
the remaining model proof can import them without a cycle.

Sources: GLS3 §§1.12.5–6 and 2.6.2; Aschbacher–Smith A.2.17, printed p.39.
-/
