module

public import Theory.SpecificGroups.Monster.Construction.NOctad.TransformCoordinates

/-!
# The octad summand of the Griess space

This interface exports the literal `B_Z`, its inclusion in the fixed Griess
space, the induced source forms, and its orthogonal decomposition over the
actual Golay octads. Each block has an orthonormal basis indexed by the 64
even subsets modulo complementation. Its coordinate functionals are the
pairings with the existing gamma, and the cubic is the existing short cubic.

The local-extension interface uses the actual `N1 → C` map and proves
descent to the literal `N/K` for any genuine extension. The coordinate
interface for `psi_3(alpha_x)` preserves the source factor one eighth and
both signed-lift conventions. Construction of the extension, its invariance
under all of N, and the sign values of the transform coefficients remain
separate obligations; the conditional interfaces do not assert them.

Source: Aschbacher, *Sporadic Groups*, 29.12–29.14 and 30.1, printed
pp. 160–163 (PDF pages 86–87).
-/
