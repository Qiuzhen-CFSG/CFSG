module

public import Theory.SpecificGroups.PSL3.LinearThreeSylow.OrdinaryComplement
import all Theory.SpecificGroups.PSL3.LinearThreeSylow.OrdinaryComplement

/-!
# The projective matrix represented by the complement torus

This companion supplies the equation identifying `complementTorus` with the
projective point torus. The internal import accesses its defining body only
to prove this public equation, preserving the original module's boundary.
The scalar action calculation for Aschbacher–Smith E.6.8 uses this equation.
-/

public section
open scoped MatrixGroups
namespace Matrix.PSL3.LinearThree.RootScalars
variable (F : Type*) [Field F]

theorem complementTorus_apply (a : Fˣ) :
    complementTorus F a = projection F (pointTorus F a) := by rfl

end Matrix.PSL3.LinearThree.RootScalars
