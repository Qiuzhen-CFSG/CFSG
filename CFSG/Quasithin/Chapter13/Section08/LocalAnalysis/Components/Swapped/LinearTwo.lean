module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.Orbit
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.Projection
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelLift
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.MaximalSection
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.SeedProjection

/-!+# The swapped linear-two reduction in 13.8.16

The residual argument puts L₁ inside the moving component orbit. The Borel
lift is taken inside that orbit, and its solvable normalized overgroup is
subject to 13.8.13. Concrete PSL₂ Cartan restrictions give the even-exponent
step, with a separate arithmetic lemma for the final three-power collapse.

The linear argument constructs the actual quotient projection for a sum
of the two factor modules. Its nonzero seed image and the marked diagonal
coset calculation exclude compatible sums even when their intersection
is nonzero. Maximal avoiding submodules and the equivariant injective
projection of an irreducible seed are also constructed.

The source Borel and diagonal markings, the inversion argument producing
the three-power Cartan order, and the actual F.9.18/B.5 module alternatives
remain to be constructed before the full orthogonal alternative can be
exported. This module does not yet assert that source conclusion. The
independent orthogonal model contradiction belongs to the parent task.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 13.8.16(1), printed p.952 (PDF p.969).
-/
