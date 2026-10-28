module

public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.source_fiber_regular_morphism
public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.sourceRelativeRootLayer_root_mem

/-!
# Construction of the source relative-root fiber module

For a relative-root representation source, the selected adjacent source-layer
quotient is the multiplicative group of the finite-dimensional exact-height
coordinate submodule supported on the chosen relative-root fiber.  The source
Levi preserves that submodule, so the rational coordinate representation
restricts to it.  Transporting the maintained left-conjugation action through
the supported-coordinate equivalence then gives all compatibility fields of
`RelativeRootFiberModule`.

The root-parameter linear maps are the individual supported coordinate axes.
The generator formulas therefore follow from the exact-layer Chevalley
coordinate calculation, while the conjugated-generator formula is represented
by the actual element `l * x_gamma(t) * l⁻¹` of the source layer.  This is the
elementary fiber-module construction used before GLS3, Theorem 1.14.7; it does
not use that theorem or any later irreducibility or highest-weight result.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

private noncomputable def sourceFiberRootParameterLinear
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (gamma : {gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root}) :
    k →ₗ[k] sourceRelativeRootFiberCoordinateSubmodule S := by
  classical
  letI : DecidableEq (RelativeRootSourceExactIndex S) := Classical.decEq _
  exact (LinearMap.single k (fun _ : RelativeRootSourceExactIndex S => k)
    (⟨gamma.1, gamma.2.2⟩ : RelativeRootSourceExactIndex S)).codRestrict
      (sourceRelativeRootFiberCoordinateSubmodule S)
      (fun t => by
        simpa only [LinearMap.single_apply] using
          sourceRelativeRootFiberCoordinateSubmodule_single_mem S gamma t)

/-- The canonical module on a source relative-root fiber: supported
exact-height coordinates with the restricted source-Levi action. -/
public noncomputable def sourceRelativeRootFiberModule
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    RelativeRootFiberModule S where
  V := sourceRelativeRootFiberCoordinateSubmodule S
  pointEquiv := relativeRootFiberSupportedCoordinateEquiv S
  coordinateLinearEquiv := relativeRootFiberCoordinateSupportedLinearEquiv S
  pointEquiv_coordinate := relativeRootFiberSupportedCoordinateEquiv_factorization S
  representation := S.sourceFiberCoordinateRepresentation
  conjugationAction := S.sourceFiberConjugationHom
  conjugatedGenerator := fun l z =>
    S.sourceFiberConjugationHom l (relativeRootFiberQuotientGenerator S z)
  conjugatedGenerator_value := S.sourceFiberConjugationHom_generator_value
  conjugationAction_generator := by intros; rfl
  representation_agrees_with_conjugation := by
    intro l q
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    rw [S.sourceFiberConjugationHom_coordinate]
    exact (S.sourceFiberCoordinateRepresentation_restricts l
      (Multiplicative.toAdd (relativeRootFiberSupportedCoordinateEquiv S q))).symm
  rootParameterLinear := sourceFiberRootParameterLinear S
  rootParameterLinear_value := by
    intro gamma t
    classical
    let _ : DecidableEq (RelativeRootSourceExactIndex S) := Classical.decEq _
    apply Subtype.ext
    rw [relativeRootFiberSupportedCoordinateEquiv_generator]
    simp only [sourceFiberRootParameterLinear, LinearMap.codRestrict_apply,
      LinearMap.single_apply, toAdd_ofAdd]

/-- Every representation source has a finite-dimensional module on its actual
relative-root fiber quotient. -/
public theorem sourceRelativeRootFiberModule_nonempty
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    Nonempty (RelativeRootFiberModule.{u, u} S) :=
  ⟨sourceRelativeRootFiberModule S⟩

end Theory.AlgebraicGroup
