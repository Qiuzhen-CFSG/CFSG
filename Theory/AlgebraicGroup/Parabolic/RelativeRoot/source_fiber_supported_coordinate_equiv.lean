module

public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.source_coordinate_fiber_stability

/-!
# Supported coordinates for a source relative-root fiber

For a relative-root representation source `S`, the chosen fiber quotient is
multiplicatively equivalent to the additive coordinate submodule supported on
that fiber.  The construction extends the existing fiber-indexed quotient
coordinates by zero, so its coercion to the full exact-height coordinate space
is exactly `relativeRootLayerQuotient_coordinateEquiv S`.

The generator formulas identify each fiber root element with the corresponding
single supported coordinate.  This supplies the coordinate model needed to
transport later Levi conjugation actions to the fiber representation in the
development following GLS3, Section 1.14.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

set_option linter.style.haveILetI false

private noncomputable def relativeRootFiberCoordinateSupportedLinearMap
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    RelativeRootFiberCoordinate S →ₗ[k]
      sourceRelativeRootFiberCoordinateSubmodule S :=
  (relativeRootFiberCoordinateExtension S).codRestrict
    (sourceRelativeRootFiberCoordinateSubmodule S) (by
      intro a
      apply (sourceRelativeRootFiberCoordinateSubmodule_mem_iff S _).2
      intro eta heta
      exact relativeRootFiberCoordinateExtension_apply_of_not_mem S a eta heta)

omit [IsAlgClosed k] in
private theorem relativeRootFiberCoordinateSupportedLinearMap_coe
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (a : RelativeRootFiberCoordinate S) :
    ((relativeRootFiberCoordinateSupportedLinearMap S a :
      sourceRelativeRootFiberCoordinateSubmodule S) :
        RelativeRootSourceExactIndex S → k) =
      relativeRootFiberCoordinateExtension S a := by
  rfl

omit [IsAlgClosed k] in
private theorem relativeRootFiberCoordinateSupportedLinearMap_injective
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    Function.Injective (relativeRootFiberCoordinateSupportedLinearMap S) := by
  intro a b hab
  funext gamma
  let eta : RelativeRootSourceExactIndex S := ⟨gamma.1, gamma.2.2⟩
  have hcoe := congrArg Subtype.val hab
  have happ := congrFun hcoe eta
  rw [relativeRootFiberCoordinateSupportedLinearMap_coe S a,
    relativeRootFiberCoordinateSupportedLinearMap_coe S b,
    relativeRootFiberCoordinateExtension_apply_of_mem S a eta gamma.2,
    relativeRootFiberCoordinateExtension_apply_of_mem S b eta gamma.2] at happ
  exact happ

omit [IsAlgClosed k] in
private theorem relativeRootFiberCoordinateSupportedLinearMap_surjective
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    Function.Surjective (relativeRootFiberCoordinateSupportedLinearMap S) := by
  intro v
  let a : RelativeRootFiberCoordinate S :=
    fun gamma => (v : RelativeRootSourceExactIndex S → k) ⟨gamma.1, gamma.2.2⟩
  refine ⟨a, ?_⟩
  apply Subtype.ext
  rw [relativeRootFiberCoordinateSupportedLinearMap_coe]
  funext eta
  by_cases heta : eta.1 ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root
  · rw [relativeRootFiberCoordinateExtension_apply_of_mem S a eta heta]
  · rw [relativeRootFiberCoordinateExtension_apply_of_not_mem S a eta heta]
    exact ((sourceRelativeRootFiberCoordinateSubmodule_mem_iff S _).1
      v.property eta heta).symm

/-- Extension by zero identifies the fiber-indexed coordinate space linearly
with the exact-height coordinate submodule supported on that fiber. -/
public noncomputable def relativeRootFiberCoordinateSupportedLinearEquiv
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    RelativeRootFiberCoordinate S ≃ₗ[k]
      sourceRelativeRootFiberCoordinateSubmodule S :=
  LinearEquiv.ofBijective (relativeRootFiberCoordinateSupportedLinearMap S)
    ⟨relativeRootFiberCoordinateSupportedLinearMap_injective S,
      relativeRootFiberCoordinateSupportedLinearMap_surjective S⟩

omit [IsAlgClosed k] in
private theorem relativeRootFiberCoordinateSupportedLinearEquiv_coe
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (a : RelativeRootFiberCoordinate S) :
    ((relativeRootFiberCoordinateSupportedLinearEquiv S a :
      sourceRelativeRootFiberCoordinateSubmodule S) :
        RelativeRootSourceExactIndex S → k) =
      relativeRootFiberCoordinateExtension S a := by
  exact relativeRootFiberCoordinateSupportedLinearMap_coe S a

/-- The source fiber quotient in its supported exact-height coordinates. -/
public noncomputable def relativeRootFiberSupportedCoordinateEquiv
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    relativeRootFiberQuotientSubgroup S ≃*
      Multiplicative (sourceRelativeRootFiberCoordinateSubmodule S) :=
  (relativeRootFiberQuotientCoordinateEquiv S).trans
    (AddEquiv.toMultiplicative
      (relativeRootFiberCoordinateSupportedLinearEquiv S).toAddEquiv)

/-- The supported-coordinate point equivalence is the canonical source fiber
coordinate equivalence followed by extension by zero.  This identifies the
entire equivalence, rather than only its values on root generators. -/
public theorem relativeRootFiberSupportedCoordinateEquiv_factorization
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (q : relativeRootFiberQuotientSubgroup S) :
    relativeRootFiberSupportedCoordinateEquiv S q =
      AddEquiv.toMultiplicative
        (relativeRootFiberCoordinateSupportedLinearEquiv S).toAddEquiv
        (relativeRootFiberQuotientCoordinateEquiv S q) := by
  rfl

/-- Coercing the supported fiber coordinates to the ambient exact-height space
recovers the existing coordinate equivalence for the full layer quotient. -/
public theorem relativeRootFiberSupportedCoordinateEquiv_coe
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (q : relativeRootFiberQuotientSubgroup S) :
    ((Multiplicative.toAdd (relativeRootFiberSupportedCoordinateEquiv S q) :
      sourceRelativeRootFiberCoordinateSubmodule S) :
        RelativeRootSourceExactIndex S → k) =
      Multiplicative.toAdd
        (relativeRootLayerQuotient_coordinateEquiv S
          (q : relativeRootLayerQuotient S)) := by
  have hcoord := relativeRootFiberCoordinateHom_coordinates S
    (relativeRootFiberQuotientCoordinateEquiv S q)
  rw [relativeRootFiberCoordinateHom_equiv_apply S q] at hcoord
  change ((relativeRootFiberCoordinateSupportedLinearEquiv S
      (relativeRootFiberQuotientCoordinateEquiv S q).toAdd :
        sourceRelativeRootFiberCoordinateSubmodule S) :
          RelativeRootSourceExactIndex S → k) = _
  rw [relativeRootFiberCoordinateSupportedLinearEquiv_coe]
  exact hcoord.symm

/-- A fiber quotient generator has the single supported coordinate indexed by
its root. -/
public theorem relativeRootFiberSupportedCoordinateEquiv_generator
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (gamma : {gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root}) (t : k) :
    letI : DecidableEq (RelativeRootSourceExactIndex S) := Classical.decEq _
    relativeRootFiberSupportedCoordinateEquiv S
        (relativeRootFiberQuotientGenerator S (gamma, t)) =
      Multiplicative.ofAdd
        (⟨Pi.single (⟨gamma.1, gamma.2.2⟩ : RelativeRootSourceExactIndex S) t,
          sourceRelativeRootFiberCoordinateSubmodule_single_mem S gamma t⟩ :
            sourceRelativeRootFiberCoordinateSubmodule S) := by
  classical
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  rw [relativeRootFiberSupportedCoordinateEquiv_coe]
  rw [relativeRootFiberQuotientGenerator_coe]
  have helem : relativeRootLayerElement S gamma.1 gamma.2 t =
      relativeRootLayerExactElement S ⟨gamma.1, gamma.2.2⟩ t := by
    apply Subtype.ext
    rw [relativeRootLayerElement_coe, relativeRootLayerExactElement_value]
  rw [helem]
  exact congrArg Multiplicative.toAdd
    (relativeRootLayerQuotient_coordinateEquiv_root S
      ⟨gamma.1, gamma.2.2⟩ t)

/-- Pointwise form of the supported coordinate formula for a fiber quotient
generator. -/
public theorem relativeRootFiberSupportedCoordinateEquiv_generator_apply
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (gamma : {gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root}) (t : k)
    (eta : RelativeRootSourceExactIndex S) :
    letI : DecidableEq (RelativeRootSourceExactIndex S) := Classical.decEq _
    ((Multiplicative.toAdd
      (relativeRootFiberSupportedCoordinateEquiv S
        (relativeRootFiberQuotientGenerator S (gamma, t))) :
        sourceRelativeRootFiberCoordinateSubmodule S) :
          RelativeRootSourceExactIndex S → k) eta =
      if eta = ⟨gamma.1, gamma.2.2⟩ then t else 0 := by
  letI : DecidableEq (RelativeRootSourceExactIndex S) := Classical.decEq _
  rw [relativeRootFiberSupportedCoordinateEquiv_generator]
  change (Pi.single
    (⟨gamma.1, gamma.2.2⟩ : RelativeRootSourceExactIndex S) t :
      RelativeRootSourceExactIndex S → k) eta = _
  by_cases h : eta = ⟨gamma.1, gamma.2.2⟩
  · subst eta
    simp
  · simp [Pi.single, h]

end Theory.AlgebraicGroup
