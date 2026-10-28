module

public import Theory.Representation.HermitianTensorThree.ParabolicTorus.OddExponent
public import Theory.Representation.HermitianTensorThree.ParabolicTorus.OddExponent.Recovery
public import Theory.Representation.HermitianTensorThree.ParabolicTorus.LargeFixed
public import Theory.SpecificGroups.GL3.BinaryParabolicOddExponent

/-!
# Completed odd parabolic geometry for the Hermitian tensor

The literal parabolic normalizer recovers its natural point or plane.
The odd order of a natural parabolic element divides q²−1, including
nonsplit two-dimensional blocks. Combined with coefficient removal and
the norm-one scalar kernel, this proves the exponent bound for both
parabolic types and all their marked cover conjugates.

Together with the large fixed-space calculation, this discharges the two
geometric inputs to the intermediate-torus step in Aschbacher–Smith 8.2.3,
printed pp.715–716. The source construction of that torus and the endpoint
fixed-space exclusion are separate.
-/

public noncomputable section
namespace Representation.HermitianTensorThree.ParabolicTorus
open OddExponent
variable (n : ℕ) [NeZero n]

/-- The natural matrix bound over the actual extension field. -/
theorem naturalParabolicOddExponent : NaturalParabolicOddExponent n := by
  intro g ho hp
  have h := Matrix.GeneralLinearGroup.binary_parabolic_odd_order_dvd g ho hp
  simpa only [card_E,←pow_mul,show 2*n*2 = 4*n by omega] using h

/-- The odd parabolic exponent on the original binary Hermitian normalizer,
with its coefficient action, central kernel and parabolic conjugates retained. -/
theorem oddLinearParabolicExponent : OddLinearParabolicExponent n :=
  oddLinearParabolicExponent_of_matrix_inputs n (congruenceParabolicRecovery n)
    (naturalParabolicOddExponent n)

end Representation.HermitianTensorThree.ParabolicTorus
