module

public import CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.DihedralInspection.FieldConstruction

/-!
# The dihedral multiplicity argument in Proposition 8.2.8(1)

The literal D₁₀ quotient gives the cyclic residual quotient and hence the
commuting K- and X-actions on P/U. From a field-generator marking of that
X-action, the scalar-refinement constructor supplies an F-linear K-action,
its exact commutator kernel, determinant one, and its simultaneous action
on the original U. Field order 16 and the two source section orders give
multiplicity dimension two or three.

This is partial infrastructure for the final paragraph on printed p.719
(PDF p.736) of Aschbacher–Smith, combined manuscript of 1 March 2004.
The field-generator marking has not yet been constructed from the genuine
X-constituent and tensor markings. The odd-prime rank deduction and the
compatible overgroup exclusions remain to be proved. In particular this
module does not assert actionImage K U ≤ actionImage (localResidual L U) U,
or Proposition 8.2.8(1). The code row requires care: 8.2.8(6) excludes a
T-action on X, and none is assumed here. Final assembly of the dihedral
inspection remains in this module.
-/
