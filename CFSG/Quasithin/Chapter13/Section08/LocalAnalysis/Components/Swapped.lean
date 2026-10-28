module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.Orbit
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.Projection
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.CriticalSubspace

/-!
# Swapped components in the proof of 13.8.16

The imported deductions construct the two-component orbit from the precise
normalizer-index alternative in 1.2.1(3), preserve relative component
membership in the generated Hz overgroup, and prove the final Sylow step
from a trivial T-orbit to normality inside H. They also establish the
diagonal projection argument for compatible product actions and the
critical-line dimension bound used in the orthogonal branch.

The L₃(2) automizer contradiction, the L₂ Borel and diagonal constructions,
and the actual eight-dimensional orthogonal model calculations remain
assembly obligations. In particular no conclusion of 13.8.16 is asserted
from these intermediate lemmas alone. Quasisimplicity of the actual K*
and exclusion of the Suzuki quotient remain inputs of the planned
non-Suzuki implication, to be supplied by its parent assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 13.8.16(1), printed pp.952–953 (PDF pp.969–970).
The Borel subgroup B in that proof is O²(B₀), the two-residual.
-/
