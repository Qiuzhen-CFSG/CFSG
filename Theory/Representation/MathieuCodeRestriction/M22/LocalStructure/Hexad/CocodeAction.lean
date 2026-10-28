module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.CocodeAction.Centralizers
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.CocodeAction.SixPointModel
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.CocodeAction.LiteralAxis

/-!
# Cocode actions for the compatible M22 hexad

This endpoint assembles the conditional action transfer on the actual cocode
quotient for native M22 and the literal setwise pair group. Six-coordinate
restriction gives the five-dimensional deleted module, with faithful actions
of the intrinsic stabilizer quotients A6 and S6. Its perfect pairing identifies
it with the dual of the orthogonal pair perpendicular; the quadratic form is
not descended through the nonsingular pair line.

Pair-class rigidity detects the intrinsic kernel and excludes shears before
descending the M24 pointwise-centralizer theorem. The canonical iterated
quotient transports every transvection, with axis the actual fixed-space span
modulo the common fixed space. The kernel identification with this literal
quotient respects stabilizer conjugation and the original cocode action on
representatives. Only the specified earlier M24 and H.14 inputs remain.

Source: Aschbacher--Smith, H.15.2(2),(5),(6), printed pp.398--399,
combined manuscript of 1 March 2004.
-/
