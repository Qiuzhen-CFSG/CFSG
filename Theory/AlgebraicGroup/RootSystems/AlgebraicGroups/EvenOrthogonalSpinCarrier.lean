module

public import Theory.AlgebraicGroup.RootSystems.CliffordSplitSpinCarrier

/-!
# The even-orthogonal Spin carrier package

For a finite-dimensional quadratic space over an algebraically closed field,
an explicit `SplitQuadraticForm` witness gives a characteristic-free PBW basis
of its Clifford algebra.  `CliffordSplitSpinCarrier` uses that basis to cut out
the exact left-regular image of Mathlib's generated `spinGroup` as a Zariski-
closed subgroup of the corresponding general-linear variety.

This module packages that construction with the field names and dependent
basis choices needed by `EvenOrthogonalModel`: membership in `spin` is stated
using the same `cliffordBasis`, carrier points are multiplicatively equivalent
to `spinGroup`, and the equivalence agrees with ambient left multiplication.
The input-space basis is included so the package can be combined with the
quadratic-isometry carrier without making a second basis choice.  The
mathematical closedness argument and its rank-zero case remain in the lower
Clifford carrier module; this is the coherent model-facing interface.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k V : Type u} [Field k] [IsAlgClosed k]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The closed Spin carrier data required by an even-orthogonal model.

The membership and ambient-point fields intentionally share `cliffordBasis`;
this records the dependent basis compatibility needed when the data are used
as the Spin fields of `EvenOrthogonalModel`. -/
public structure EvenOrthogonalSpinCarrier
    (Q : QuadraticForm k V) where
  basis : Module.Basis (Fin (Module.finrank k V)) k V
  cliffordBasis : Module.Basis
    (Fin (Module.finrank k (CliffordAlgebra Q))) k (CliffordAlgebra Q)
  spin : ClosedSubgroup (glVarietyOf k (CliffordAlgebra Q))
  spin_carrier : ∀ g, g ∈ spin.toSubgroup ↔
      ∃ x : spinGroup Q,
        LinearMap.GeneralLinearGroup.generalLinearEquiv k (CliffordAlgebra Q)
            (glPointEquivOf k (CliffordAlgebra Q) cliffordBasis g) =
          (spinGroup.toUnits x).mulLeftLinearEquiv k (CliffordAlgebra Q)
  spinPoints : let := spin.carrierAlgebraicGroup
    Variety.Point spin.carrierVariety ≃* spinGroup Q
  spinLinear_points :
    letI := spin.carrierAlgebraicGroup
    ∀ x,
      LinearMap.GeneralLinearGroup.generalLinearEquiv k (CliffordAlgebra Q)
          (glPointEquivOf k (CliffordAlgebra Q) cliffordBasis
            (spin.inclusion.onPoints x)) =
        (spinGroup.toUnits (spinPoints x)).mulLeftLinearEquiv
          k (CliffordAlgebra Q)

/-- The exact split Clifford carrier, packaged with precisely the bases used
by the even-orthogonal model interface. -/
public noncomputable def splitEvenOrthogonalSpinCarrier
    {Q : QuadraticForm k V} (s : SplitQuadraticForm Q) :
    EvenOrthogonalSpinCarrier Q where
  basis := Module.finBasis k V
  cliffordBasis := splitSpinCliffordBasis s
  spin := splitSpinClosedSubgroup s
  spin_carrier := splitSpinClosedSubgroup_carrier s
  spinPoints := splitSpinClosedSubgroupPoints s
  spinLinear_points := splitSpinClosedSubgroup_linear_points s

/-- The packaged input-space basis is the canonical finite basis used to form
the split Clifford PBW basis. -/
@[simp]
public theorem splitEvenOrthogonalSpinCarrier_basis
    {Q : QuadraticForm k V} (s : SplitQuadraticForm Q) :
    (splitEvenOrthogonalSpinCarrier s).basis = Module.finBasis k V := by
  rfl

/-- The packaged Clifford basis is exactly the split PBW basis used in the
closed-carrier equations. -/
@[simp]
public theorem splitEvenOrthogonalSpinCarrier_cliffordBasis
    {Q : QuadraticForm k V} (s : SplitQuadraticForm Q) :
    (splitEvenOrthogonalSpinCarrier s).cliffordBasis =
      splitSpinCliffordBasis s := by
  rfl

/-- The packaged subgroup is the exact closed left-regular split Spin
carrier. -/
@[simp]
public theorem splitEvenOrthogonalSpinCarrier_spin
    {Q : QuadraticForm k V} (s : SplitQuadraticForm Q) :
    (splitEvenOrthogonalSpinCarrier s).spin =
      splitSpinClosedSubgroup s := by
  rfl

end Theory.AlgebraicGroup
