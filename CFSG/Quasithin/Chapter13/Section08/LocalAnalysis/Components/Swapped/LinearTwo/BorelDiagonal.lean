module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.SourceBorel
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.LiftedTorus
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.CoveredAlternative
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.Residuals
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.ProjectedImages
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.CartanAction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.CommutatorPrimes
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.SourceAssembly

/-!
# Borel and marked diagonal deductions for the moving linear-two orbit

SourceConclusion.exists_borel_diagonal constructs the marked product
coordinates and the Borel through the source Sylow intersection, proves
normalization and containment in M, and derives even n and three-rank two.
The theta identity excludes the ordinary A₆ quotient. The genuine covered
natural action supplies the marked cubic quotients and inverter; the actual
commutator then forces the Cartan three-power and n = 2. Finally L₁ equals
O²(B₀), and the full marked star images have equal first projections, with
kernel exactly the second component. The intrinsic two-core quotients are
kept separate from the full marked groups throughout.

The earlier source identities and natural setup remain explicit inputs for
the parent. No Borel, diagonal, action identity, or parameter conclusion is
assumed. Module classification and the orthogonal contradiction are outside
this group-theoretic assembly.

Source: Aschbacher–Smith, proof of 13.8.16(1), printed p.952/PDF p.969,
with Notation 13.2.1, printed p.877.
-/
