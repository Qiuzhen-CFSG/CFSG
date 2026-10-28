module

public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.source_layer_levi_action
public import Theory.AlgebraicGroup.Representations.Operations

/-!
# Regular source-Levi action on supported fiber coordinates

For a relative-root representation source `S`, this module restricts the
regular action on all exact-height coordinates to the canonical submodule
supported on the chosen relative-root fiber.  It exposes the resulting
rational representation, a basis, and an algebraic-group morphism from the
source Levi to the general linear group of that supported submodule.

The final construction changes from supported coordinates to any
finite-dimensional vector space linearly equivalent to the canonical fiber
coordinates.  Its matrix coefficients are pulled back from the supported
morphism, and its point action is conjugation by the supplied linear
equivalence.  Thus the resulting public morphism to the new general linear
group still acts pointwise by source fiber conjugation.

The supported submodule is invariant by the source coordinate-stability
theorem.  The general restriction construction for rational representations
therefore supplies the morphism.  Its rational-point action is identified
first with the restricted full coordinate action and then, through
`relativeRootFiberSupportedCoordinateEquiv`, with the concrete source fiber
conjugation homomorphism.  This is the source-coordinate geometric input used
for the relative-root fiber rationality argument following GLS3, Section 1.14;
it is independent of `RelativeRootFiberModule` and the numbered theorems.
-/

universe u v

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The supported fiber-coordinate submodule is invariant under the regular
source exact-layer coordinate representation. -/
public theorem
    RelativeRootRepresentationSource.sourceFiberCoordinateSubmodule_invariant
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    IsInvariantSubmodule S.sourceLayerCoordinateRationalRepresentation
      (sourceRelativeRootFiberCoordinateSubmodule S) := by
  intro l v hv
  have hm :
      (S.sourceLayerCoordinateRationalRepresentation.action l :
        Module.End k (RelativeRootSourceExactIndex S -> k)) v ∈
        Submodule.map
          (S.sourceLayerCoordinateRationalRepresentation.action l :
            Module.End k (RelativeRootSourceExactIndex S -> k))
          (sourceRelativeRootFiberCoordinateSubmodule S) :=
    Submodule.mem_map_of_mem hv
  rwa [sourceRelativeRootFiberCoordinateSubmodule_stable S l] at hm

/-- The source exact-layer coordinate representation restricted to the
canonical supported fiber-coordinate submodule. -/
public noncomputable def
    RelativeRootRepresentationSource.sourceFiberCoordinateRepresentation
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    RationalRepresentation S.L.carrierVariety
      (sourceRelativeRootFiberCoordinateSubmodule S) :=
  Classical.choose (rationalRepresentation_restriction_exists
    S.sourceLayerCoordinateRationalRepresentation
    S.sourceLayerCoordinateRationalRepresentation_isRational
    (sourceRelativeRootFiberCoordinateSubmodule S)
    S.sourceFiberCoordinateSubmodule_invariant)

/-- The supported fiber-coordinate representation is the restriction of the
full exact-layer coordinate representation. -/
public theorem
    RelativeRootRepresentationSource.sourceFiberCoordinateRepresentation_restricts
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    IsRestrictionRepresentation S.sourceLayerCoordinateRationalRepresentation
      (sourceRelativeRootFiberCoordinateSubmodule S)
      S.sourceFiberCoordinateRepresentation :=
  (Classical.choose_spec (rationalRepresentation_restriction_exists
    S.sourceLayerCoordinateRationalRepresentation
    S.sourceLayerCoordinateRationalRepresentation_isRational
    (sourceRelativeRootFiberCoordinateSubmodule S)
    S.sourceFiberCoordinateSubmodule_invariant)).1

/-- The restricted supported-coordinate representation is rational. -/
public theorem
    RelativeRootRepresentationSource.sourceFiberCoordinateRepresentation_isRational
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    IsRationalRepresentation S.sourceFiberCoordinateRepresentation :=
  (Classical.choose_spec (rationalRepresentation_restriction_exists
    S.sourceLayerCoordinateRationalRepresentation
    S.sourceLayerCoordinateRationalRepresentation_isRational
    (sourceRelativeRootFiberCoordinateSubmodule S)
    S.sourceFiberCoordinateSubmodule_invariant)).2

/-- A basis in which the regular supported-coordinate action is realized. -/
public noncomputable def
    RelativeRootRepresentationSource.sourceFiberCoordinateBasis
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    Module.Basis
      (Fin (Module.finrank k (sourceRelativeRootFiberCoordinateSubmodule S)))
      k (sourceRelativeRootFiberCoordinateSubmodule S) :=
  Classical.choose S.sourceFiberCoordinateRepresentation_isRational

/-- The algebraic-group morphism realizing source fiber conjugation on the
canonical supported fiber-coordinate submodule. -/
public noncomputable def
    RelativeRootRepresentationSource.sourceFiberCoordinateMorphism
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    AlgebraicGroup.Morphism S.L.carrierVariety
      (glVarietyOf k (sourceRelativeRootFiberCoordinateSubmodule S)) :=
  Classical.choose
    (Classical.choose_spec S.sourceFiberCoordinateRepresentation_isRational)

/-- On rational points, the supported-coordinate morphism recovers the
restricted linear representation. -/
public theorem
    RelativeRootRepresentationSource.sourceFiberCoordinateMorphism_onPoints
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (l : Variety.Point S.L.carrierVariety) :
    glPointEquivOf k (sourceRelativeRootFiberCoordinateSubmodule S)
        S.sourceFiberCoordinateBasis (S.sourceFiberCoordinateMorphism.onPoints l) =
      S.sourceFiberCoordinateRepresentation.action l :=
  Classical.choose_spec
    (Classical.choose_spec S.sourceFiberCoordinateRepresentation_isRational) l

/-- Pointwise supported-coordinate formula: the regular linear action is
exactly source fiber conjugation transported through the canonical coordinate
equivalence. -/
public theorem
    RelativeRootRepresentationSource.sourceFiberCoordinateMorphism_point_action
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (l : Variety.Point S.L.carrierVariety)
    (q : relativeRootFiberQuotientSubgroup S) :
    Multiplicative.ofAdd
        ((glPointEquivOf k (sourceRelativeRootFiberCoordinateSubmodule S)
          S.sourceFiberCoordinateBasis
          (S.sourceFiberCoordinateMorphism.onPoints l)).1
            (Multiplicative.toAdd
              (relativeRootFiberSupportedCoordinateEquiv S q))) =
      relativeRootFiberSupportedCoordinateEquiv S
        (S.sourceFiberConjugationHom l q) := by
  apply Multiplicative.toAdd.injective
  rw [S.sourceFiberCoordinateMorphism_onPoints]
  apply Subtype.ext
  exact (S.sourceFiberCoordinateRepresentation_restricts l
      (Multiplicative.toAdd (relativeRootFiberSupportedCoordinateEquiv S q))).trans
    (S.sourceFiberConjugationHom_coordinate l q).symm

/-! ## Transport to arbitrary linear fiber coordinates -/

/-- The change of coordinates from the supported exact-height submodule to an
arbitrary linear model of the canonical fiber coordinates. -/
public noncomputable def
    RelativeRootRepresentationSource.sourceFiberCoordinateTransportLinearEquiv
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    {V : Type v} [AddCommGroup V] [Module k V]
    (e : RelativeRootFiberCoordinate S ≃ₗ[k] V) :
    sourceRelativeRootFiberCoordinateSubmodule S ≃ₗ[k] V :=
  (relativeRootFiberCoordinateSupportedLinearEquiv S).symm.trans e

/-- A finite basis used to realize the transported source fiber action as a
morphism to the general linear group of the target coordinate space. -/
public noncomputable def
    RelativeRootRepresentationSource.sourceFiberCoordinateTransportBasis
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (_e : RelativeRootFiberCoordinate S ≃ₗ[k] V) :
    Module.Basis (Fin (Module.finrank k V)) k V :=
  Module.finBasis k V

private noncomputable def
    RelativeRootRepresentationSource.sourceFiberCoordinateTransportAction
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    {V : Type v} [AddCommGroup V] [Module k V]
    (e : RelativeRootFiberCoordinate S ≃ₗ[k] V) :
    Variety.Point S.L.carrierVariety →*
      LinearMap.GeneralLinearGroup k V :=
  (LinearMap.GeneralLinearGroup.congrLinearEquiv
      (S.sourceFiberCoordinateTransportLinearEquiv e)).toMonoidHom.comp
    S.sourceFiberCoordinateRepresentation.action

private theorem
    RelativeRootRepresentationSource.sourceFiberCoordinateTransportAction_apply
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    {V : Type v} [AddCommGroup V] [Module k V]
    (e : RelativeRootFiberCoordinate S ≃ₗ[k] V)
    (l : Variety.Point S.L.carrierVariety) (x : V) :
    ((S.sourceFiberCoordinateTransportAction e l :
        LinearMap.GeneralLinearGroup k V) : Module.End k V) x =
      S.sourceFiberCoordinateTransportLinearEquiv e
        ((S.sourceFiberCoordinateRepresentation.action l :
            Module.End k (sourceRelativeRootFiberCoordinateSubmodule S))
          ((S.sourceFiberCoordinateTransportLinearEquiv e).symm x)) := by
  rfl

private noncomputable def
    RelativeRootRepresentationSource.sourceFiberCoordinateTransportMatrixCoefficient
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (e : RelativeRootFiberCoordinate S ≃ₗ[k] V)
    (i j : Fin (Module.finrank k V)) :
    S.L.carrierVariety.PolynomialFunction :=
  rationalRepresentationLinearMatrixCoefficient
    S.sourceFiberCoordinateRepresentation
    S.sourceFiberCoordinateBasis
    S.sourceFiberCoordinateMorphism
    (((S.sourceFiberCoordinateTransportBasis e).coord i).comp
      (S.sourceFiberCoordinateTransportLinearEquiv e).toLinearMap)
    ((S.sourceFiberCoordinateTransportLinearEquiv e).symm
      (S.sourceFiberCoordinateTransportBasis e j))

private theorem
    RelativeRootRepresentationSource.sourceFiberCoordinateTransportMatrixCoefficient_apply
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (e : RelativeRootFiberCoordinate S ≃ₗ[k] V)
    (i j : Fin (Module.finrank k V))
    (l : Variety.Point S.L.carrierVariety) :
    S.sourceFiberCoordinateTransportMatrixCoefficient e i j l =
      (S.sourceFiberCoordinateTransportBasis e).repr
        (((S.sourceFiberCoordinateTransportAction e l :
            LinearMap.GeneralLinearGroup k V) : Module.End k V)
          (S.sourceFiberCoordinateTransportBasis e j)) i := by
  rw [RelativeRootRepresentationSource.sourceFiberCoordinateTransportMatrixCoefficient,
    rationalRepresentationLinearMatrixCoefficient_apply
      S.sourceFiberCoordinateRepresentation
      S.sourceFiberCoordinateBasis S.sourceFiberCoordinateMorphism
      S.sourceFiberCoordinateMorphism_onPoints]
  rw [S.sourceFiberCoordinateTransportAction_apply]
  rfl

private noncomputable def
    RelativeRootRepresentationSource.sourceFiberCoordinateTransportInverseMatrixCoefficient
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (e : RelativeRootFiberCoordinate S ≃ₗ[k] V)
    (i j : Fin (Module.finrank k V)) :
    S.L.carrierVariety.PolynomialFunction :=
  Variety.PolynomialFunction.pullback
    (AlgebraicGroup.invMorphism S.L.carrierVariety)
    (S.sourceFiberCoordinateTransportMatrixCoefficient e i j)

private theorem
    RelativeRootRepresentationSource.sourceFiberCoordinateTransportInverseMatrixCoefficient_apply
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (e : RelativeRootFiberCoordinate S ≃ₗ[k] V)
    (i j : Fin (Module.finrank k V))
    (l : Variety.Point S.L.carrierVariety) :
    S.sourceFiberCoordinateTransportInverseMatrixCoefficient e i j l =
      (S.sourceFiberCoordinateTransportBasis e).repr
        ((((S.sourceFiberCoordinateTransportAction e l)⁻¹ :
            LinearMap.GeneralLinearGroup k V) : Module.End k V)
          (S.sourceFiberCoordinateTransportBasis e j)) i := by
  change S.sourceFiberCoordinateTransportMatrixCoefficient e i j l⁻¹ = _
  rw [S.sourceFiberCoordinateTransportMatrixCoefficient_apply]
  simp

/-- The canonical supported-fiber morphism transported through arbitrary
linear coordinates on the relative-root fiber. -/
public noncomputable def
    RelativeRootRepresentationSource.sourceFiberCoordinateTransportMorphism
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (e : RelativeRootFiberCoordinate S ≃ₗ[k] V) :
    AlgebraicGroup.Morphism S.L.carrierVariety (glVarietyOf k V) :=
  generalLinearRepresentationMorphismOfInverseMatrixCoefficient
    (S.sourceFiberCoordinateTransportBasis e)
    (S.sourceFiberCoordinateTransportAction e)
    (S.sourceFiberCoordinateTransportMatrixCoefficient e)
    (S.sourceFiberCoordinateTransportInverseMatrixCoefficient e)
    (S.sourceFiberCoordinateTransportMatrixCoefficient_apply e)
    (S.sourceFiberCoordinateTransportInverseMatrixCoefficient_apply e)

/-- On rational points, the transported morphism is conjugation of the
supported-coordinate linear action by the chosen change of coordinates. -/
public theorem
    RelativeRootRepresentationSource.sourceFiberCoordinateTransportMorphism_onPoints
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (e : RelativeRootFiberCoordinate S ≃ₗ[k] V)
    (l : Variety.Point S.L.carrierVariety) :
    glPointEquivOf k V (S.sourceFiberCoordinateTransportBasis e)
        ((S.sourceFiberCoordinateTransportMorphism e).onPoints l) =
      LinearMap.GeneralLinearGroup.congrLinearEquiv
        (S.sourceFiberCoordinateTransportLinearEquiv e)
        (S.sourceFiberCoordinateRepresentation.action l) := by
  change glPointEquivOf k V (S.sourceFiberCoordinateTransportBasis e)
      (generalLinearRepresentationPoint
        (S.sourceFiberCoordinateTransportBasis e)
        (S.sourceFiberCoordinateTransportAction e l)) = _
  rw [glPointEquivOf_generalLinearRepresentationPoint]
  rfl

/-- Pointwise transport formula: in arbitrary linear fiber coordinates, the
regular morphism acts exactly by source Levi conjugation on the fiber
quotient. -/
public theorem
    RelativeRootRepresentationSource.sourceFiberCoordinateTransportMorphism_point_action
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (e : RelativeRootFiberCoordinate S ≃ₗ[k] V)
    (l : Variety.Point S.L.carrierVariety)
    (q : relativeRootFiberQuotientSubgroup S) :
    Multiplicative.ofAdd
        ((glPointEquivOf k V
          (S.sourceFiberCoordinateTransportBasis e)
          ((S.sourceFiberCoordinateTransportMorphism e).onPoints l)).1
            (e (Multiplicative.toAdd
              (relativeRootFiberQuotientCoordinateEquiv S q)))) =
      AddEquiv.toMultiplicative e.toAddEquiv
        (relativeRootFiberQuotientCoordinateEquiv S
          (S.sourceFiberConjugationHom l q)) := by
  let E := S.sourceFiberCoordinateTransportLinearEquiv e
  have hE (r : relativeRootFiberQuotientSubgroup S) :
      E (Multiplicative.toAdd (relativeRootFiberSupportedCoordinateEquiv S r)) =
        e (Multiplicative.toAdd
          (relativeRootFiberQuotientCoordinateEquiv S r)) := by
    rw [relativeRootFiberSupportedCoordinateEquiv_factorization]
    change ((relativeRootFiberCoordinateSupportedLinearEquiv S).symm.trans e)
        (relativeRootFiberCoordinateSupportedLinearEquiv S
          (Multiplicative.toAdd
            (relativeRootFiberQuotientCoordinateEquiv S r))) = _
    rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  have hs := congrArg Multiplicative.toAdd
    (S.sourceFiberCoordinateMorphism_point_action l q)
  rw [S.sourceFiberCoordinateMorphism_onPoints] at hs
  apply Multiplicative.toAdd.injective
  rw [S.sourceFiberCoordinateTransportMorphism_onPoints]
  change E ((S.sourceFiberCoordinateRepresentation.action l :
      Module.End k (sourceRelativeRootFiberCoordinateSubmodule S))
        (E.symm (e (Multiplicative.toAdd
          (relativeRootFiberQuotientCoordinateEquiv S q))))) =
    e (Multiplicative.toAdd
      (relativeRootFiberQuotientCoordinateEquiv S
        (S.sourceFiberConjugationHom l q)))
  rw [← hE q, E.symm_apply_apply, ← hE (S.sourceFiberConjugationHom l q)]
  exact congrArg E hs

end Theory.AlgebraicGroup
