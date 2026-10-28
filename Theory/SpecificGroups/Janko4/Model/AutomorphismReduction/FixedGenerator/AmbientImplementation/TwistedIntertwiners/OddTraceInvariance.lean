module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.AmbientImplementation.Intertwiners
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.AmbientImplementation.TwistedIntertwiners.OddTraceInvariance.Prime31Separation

/-!+# Odd-order trace comparison for the concrete J₄ representation

The desired automorphism-invariance theorem remains open. The imported
`Prime31Separation` proves an obstruction to reducing it to element orders or
prime-order cyclic coverage: two generators of the same order-31 subgroup have
different binary traces. No automorphism taking one to the other is asserted.

GLS3, Table 5.3i, in `refs/KGroup/GLS3/Chapter5(sec3-).tex` asserts existence of
an absolutely irreducible 112-dimensional binary representation. That clause
does not assert uniqueness or identify an automorphism twist with the given
representation. The certified Mathieu quotient in `Model.LocalStructure.Mathieu`
likewise does not supply that representation comparison. The remaining
obligation concerns the literal ATLAS matrices defined in `Model.Data`.

This module imports `Intertwiners` directly so that the parent
`TwistedIntertwiners` may eventually import the completed comparison without
forming an assembly cycle. Irreducibility is not imported or asserted here.
-/
