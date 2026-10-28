module

public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Placement.Alternatives
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Placement.EightPointLine.Contracts
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Placement.EightPointLine.Coverage
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Placement.EightPointLine.Sieve

/-!
# Assembly of the eight-point invariant-line calculation

The fixed Sylow subgroup and the order-nine candidates use literal even
permutations. The proved uniform coverage and candidate sieve construct an
invariant order-three subgroup for the fixed Sylow two-subgroup. Transport
through actual A₈ conjugacy gives `eightPointPairLine` for every Sylow
two-subgroup. The conjugators preserving the line remain elements of A₈.

Source: Aschbacher–Smith, proof of 1.3.4, printed p.511 (PDF p.528);
GLS3, Table 5.3e, the octad stabilizer `E₁₆.A₈`.
-/

@[expose] public section
namespace Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement
open EightPoint

/-- Conditional assembly; both explicit finite-calculation premises are required. -/
theorem eightPointPairLine_of_coverage_sieve
    (hcover : NineCoverage) (hsieve : NineSieve) : EightPointPairLine :=
  eightPointPairLine_of_fixedSylow twoSylow
    (fixedSylowLine_of_coverage_sieve hcover hsieve)

/-- A permuting elementary nine and Sylow two-subgroup of A₈ have an
order-three subgroup invariant under their common inner normalizer. -/
theorem eightPointPairLine : EightPointPairLine :=
  eightPointPairLine_of_coverage_sieve nineCoverage nineSieve

end Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement
end
