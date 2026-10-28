module

public import CFSG.Quasithin.Chapter8.Section02.Offenders.LinearTorus
public import Theory.Representation.HermitianTensorThree.ParabolicTorus.Geometry

/-!
# The proved intermediate Hermitian torus exclusion

The large fixed-space and odd parabolic exponent calculations now discharge
both geometric inputs of the existing marked torus setup. Its original
fixed-space identity, actor degree and rank bounds exclude n < k < 2n.
With the source interval this gives the split-torus divisibility. The
endpoint k = 2n still requires the H.4.4(4) fixed-space contradiction.

These are conditional applications to the literal marked setup, not a
construction of the selected source pair or the full shadow exclusion.
Source: Aschbacher–Smith 8.2.3, printed pp.715–716.
-/

public section
namespace CFSG.Quasithin.Chapter8.Section02.Offenders.LinearThreeTorus
open Representation.HermitianTensorThree.ParabolicTorus
variable {n k : ℕ} [NeZero n]

/-- No additional geometric premise remains in the intermediate case. -/
theorem Setup.not_intermediate (s : Setup n k) (hnk : n < k) (hkn : k < 2*n) : False :=
  s.not_intermediate_of_geometry (largeOddFixedSpaceLinearity n)
    (oddLinearParabolicExponent n) hnk hkn

/-- Both marked parabolic types and their nonsplit tori are included. -/
theorem Setup.hasLinearThreeParabolicTorus (s : Setup n k)
    (hlower : n ≤ k) (hupper : k ≤ 2*n) : HasLinearThreeParabolicTorus n k :=
  s.hasLinearThreeParabolicTorus_of_geometry (largeOddFixedSpaceLinearity n)
    (oddLinearParabolicExponent n) hlower hupper

/-- The original parameter theorem now retains only its source interval and
endpoint exclusion; both model geometry premises have been proved. -/
theorem Setup.parameters (s : Setup n k) {w : ℕ}
    (hbounds : n ≤ w ∧ w ≤ k ∧ k ≤ 2*n)
    (hH44 : k = 2*n → False) : k = n ∧ w = n :=
  s.parameters_of_geometry (largeOddFixedSpaceLinearity n)
    (oddLinearParabolicExponent n) hbounds hH44

end CFSG.Quasithin.Chapter8.Section02.Offenders.LinearThreeTorus
