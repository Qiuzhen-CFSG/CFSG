module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.EvenSpinIsogeny

/-!
# The algebraic split even-orthogonal Spin model

For a finite-dimensional split quadratic space over an algebraically closed
field, this module packages the characteristic-free Clifford construction as
the Spin part of the concrete even-orthogonal model.  The package contains the
split PBW basis of the Clifford algebra, the exact closed left-regular Spin
carrier and its point equivalence, the Clifford-conjugation action on the
quadratic space, and the regular cover of its closed orthogonal image.

In hyperbolic rank at least four, the closed image has exactly the points of
the commutator subgroup of the full quadratic-isometry group.  The cover is
surjective with finite kernel, hence an isogeny, and its point formula is the
Clifford action.  Thus the package supplies precisely the non-projective fields
of `EvenOrthogonalModel`; the projective central quotient is assembled in the
higher `EvenOrthogonalOmegaModel` module.  The mathematical input is the split
Cartan--Dieudonne/Clifford factorization developed by the imported carrier,
action, and isogeny modules.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k V : Type u} [Field k] [IsAlgClosed k]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The Clifford Spin carrier, its exact derived orthogonal image, and the
algebraic Spin cover, with the dependent bases used by `EvenOrthogonalModel`.
-/
public structure EvenOrthogonalSpinModel
    (Q : QuadraticForm k V) extends EvenOrthogonalSpinCarrier Q where
  omega : ClosedSubgroup (glVarietyOf k V)
  omega_carrier : ∀ g, g ∈ omega.toSubgroup ↔
      ∃ x : commutator (quadraticIsometrySubgroup Q),
        x.1.1 = LinearMap.GeneralLinearGroup.generalLinearEquiv k V
          (glPointEquivOf k V basis g)
  omegaPoints : let := omega.carrierAlgebraicGroup
    Variety.Point omega.carrierVariety ≃*
      commutator (quadraticIsometrySubgroup Q)
  omegaLinear_points :
    letI := omega.carrierAlgebraicGroup
    ∀ x,
      LinearMap.GeneralLinearGroup.generalLinearEquiv k V
          (glPointEquivOf k V basis (omega.inclusion.onPoints x)) =
        (omegaPoints x).1.1
  spinAction : spinGroup Q →* quadraticIsometrySubgroup Q
  spinAction_clifford : ∀ x v,
    CliffordAlgebra.ι Q ((spinAction x).1 v) =
      (x : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
        (↑((spinGroup.toUnits x)⁻¹) : CliffordAlgebra Q)
  spinCover : let := spin.carrierAlgebraicGroup
    letI := omega.carrierAlgebraicGroup
    AlgebraicGroup.Morphism spin.carrierVariety omega.carrierVariety
  spinCoverIsogeny : let := spin.carrierAlgebraicGroup
    letI := omega.carrierAlgebraicGroup
    IsIsogeny spinCover
  spinCover_points :
    letI := spin.carrierAlgebraicGroup
    letI := omega.carrierAlgebraicGroup
    ∀ x, (omegaPoints (spinCover.onPoints (spinPoints.symm x))).1 =
      spinAction x

/-- Construct the genuine algebraic Spin model of a split even-dimensional
quadratic space of hyperbolic rank at least four. -/
@[expose]
public noncomputable def splitEvenOrthogonalSpinModel
    {Q : QuadraticForm k V} (s : SplitQuadraticForm Q)
    (hrank : 4 ≤ s.rank) : EvenOrthogonalSpinModel Q where
  toEvenOrthogonalSpinCarrier := {
    basis := Module.finBasis k V
    cliffordBasis := splitSpinCliffordBasis s
    spin := splitSpinClosedSubgroup s
    spin_carrier := splitSpinClosedSubgroup_carrier s
    spinPoints := splitSpinClosedSubgroupPoints s
    spinLinear_points := splitSpinClosedSubgroup_linear_points s
  }
  omega := evenSpinActionImageClosedSubgroup Q s
  omega_carrier := evenSpinActionImageClosedSubgroup_commutator_carrier Q s hrank
  omegaPoints := evenSpinActionImageClosedSubgroupPoints Q s hrank
  omegaLinear_points := evenSpinActionImageClosedSubgroup_linear_points Q s hrank
  spinAction := cliffordSpinActionOfSplit Q s
  spinAction_clifford := cliffordSpinActionOfSplit_spec Q s
  spinCover := evenSpinActionImageCover Q s
  spinCoverIsogeny := evenSpinActionImageCover_isIsogeny Q s
  spinCover_points := evenSpinActionImageCover_spin_points Q s hrank

/-- The orthogonal target of the packaged model is the exact closed image of
the split Clifford action. -/
@[simp]
public theorem splitEvenOrthogonalSpinModel_omega
    {Q : QuadraticForm k V} (s : SplitQuadraticForm Q)
    (hrank : 4 ≤ s.rank) :
    (splitEvenOrthogonalSpinModel s hrank).omega =
      evenSpinActionImageClosedSubgroup Q s := by
  rfl

end Theory.AlgebraicGroup
