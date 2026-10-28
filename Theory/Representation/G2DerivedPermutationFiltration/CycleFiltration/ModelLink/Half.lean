module

public import Theory.Representation.G2DerivedPermutationFiltration.CycleFiltration.ModelLink.Kernel
public import Theory.Representation.G2DerivedPermutationFiltration.CycleFiltration.ModelLink.GeneratorInvariance
/-!
# The invariant half and literal quotient of the binary G₂ cycle space

Pull back the certified numerical half along the equivalence with the actual
incidence kernel. Its invariance under the two derived-group generators extends
to the whole group by the established generation theorem. The numerical
projection has precisely this half as its kernel, so its surjectivity gives
coordinates on the literal quotient. The two coordinate actions are the saved
32-dimensional diagonal blocks.

Source application: Aschbacher–Smith G.7.2(3), printed p.348 / PDF p.359.
-/

@[expose] public section

namespace G2DerivedPermutationFiltration.CycleModelLink
open CycleData VertexCoordinates

/-- The certified half, as a subrepresentation of the actual boundary kernel. -/
noncomputable def invariantHalf : Subrepresentation cycleSubrepresentation.toRepresentation where
  toSubmodule := Certificate.half.comap coordinates.toLinearMap
  apply_mem_toSubmodule := by
    apply invariant_of_generators
    intro j v hv
    change coordinates (cycleSubrepresentation.toRepresentation (groupGenerator j) v) ∈ Certificate.half
    rw [coordinates_action]
    exact Certificate.action_mem_half j hv

/-- Restriction of the cycle coordinates to the invariant half. -/
noncomputable def halfEquiv : invariantHalf.toSubmodule ≃ₗ[ZMod 2] Certificate.half where
  toFun v := ⟨coordinates v.val, v.property⟩
  invFun v := ⟨coordinates.symm v.val, by
    change coordinates (coordinates.symm v.val) ∈ Certificate.half
    rw [LinearEquiv.apply_symm_apply]
    exact v.property⟩
  map_add' v w := Subtype.ext (map_add coordinates v.val w.val)
  map_smul' a v := Subtype.ext (map_smul coordinates a v.val)
  left_inv v := Subtype.ext (coordinates.symm_apply_apply v.val)
  right_inv v := Subtype.ext (coordinates.apply_symm_apply v.val)

/-- The first 32 adapted coordinates on the actual invariant half. -/
noncomputable def halfCoordinates : invariantHalf.toSubmodule ≃ₗ[ZMod 2] Half :=
  halfEquiv.trans Certificate.halfCoordinates

/-- The last 32 adapted coordinates on the actual cycle space. -/
noncomputable def quotientProjection : cycleSubrepresentation.toSubmodule →ₗ[ZMod 2] Half :=
  Certificate.projection.comp coordinates.toLinearMap

/-- Coordinates on the literal quotient by the invariant half. -/
noncomputable def quotientCoordinates :
    (cycleSubrepresentation.toSubmodule ⧸ invariantHalf.toSubmodule) ≃ₗ[ZMod 2] Half :=
  quotientProjection.quotKerEquivOfSurjective
    (Certificate.projection_surjective.comp coordinates.surjective)

@[simp] theorem quotientCoordinates_mk (v : cycleSubrepresentation.toSubmodule) :
    quotientCoordinates (Submodule.Quotient.mk v) = Certificate.projection (coordinates v) := by
  exact quotientProjection.quotKerEquivOfSurjective_apply_mk
    (Certificate.projection_surjective.comp coordinates.surjective) v

theorem halfCoordinates_action (a : Fin 2) (v : invariantHalf.toSubmodule) :
    halfCoordinates (invariantHalf.toRepresentation (groupGenerator a) v) =
      (factorMatrix 0 a).mulVec (halfCoordinates v) := by
  have h : halfEquiv (invariantHalf.toRepresentation (groupGenerator a) v) =
      Certificate.halfAction a (halfEquiv v) := by
    apply Subtype.ext
    change coordinates (cycleSubrepresentation.toRepresentation (groupGenerator a) v.val) =
      (Certificate.actionMatrix a).mulVec (coordinates v.val)
    exact coordinates_action a v.val
  exact (congrArg Certificate.halfCoordinates h).trans
    (Certificate.halfCoordinates_action a (halfEquiv v))

theorem quotientCoordinates_action (a : Fin 2)
    (v : cycleSubrepresentation.toSubmodule ⧸ invariantHalf.toSubmodule) :
    quotientCoordinates (invariantHalf.quotientRepresentation (groupGenerator a) v) =
      (factorMatrix 1 a).mulVec (quotientCoordinates v) := by
  induction v using Submodule.Quotient.induction_on with
  | H v =>
    change quotientCoordinates (Submodule.Quotient.mk
      (cycleSubrepresentation.toRepresentation (groupGenerator a) v)) = _
    rw [quotientCoordinates_mk, quotientCoordinates_mk, coordinates_action,
      Certificate.projection_action]

theorem half_factorMatrix (a : Fin 2) :
    LinearMap.toMatrix' (halfCoordinates.conj (invariantHalf.toRepresentation (groupGenerator a))) =
      factorMatrix 0 a := by
  have h : halfCoordinates.conj (invariantHalf.toRepresentation (groupGenerator a)) =
      (factorMatrix 0 a).mulVecLin := by
    apply LinearMap.ext
    intro v
    rw [LinearEquiv.conj_apply_apply]
    change halfCoordinates (invariantHalf.toRepresentation (groupGenerator a)
      (halfCoordinates.symm v)) = _
    rw [halfCoordinates_action, LinearEquiv.apply_symm_apply]
    rfl
  rw [h]
  exact LinearMap.toMatrix'_toLin' _

theorem quotient_factorMatrix (a : Fin 2) :
    LinearMap.toMatrix' (quotientCoordinates.conj
      (invariantHalf.quotientRepresentation (groupGenerator a))) = factorMatrix 1 a := by
  have h : quotientCoordinates.conj (invariantHalf.quotientRepresentation (groupGenerator a)) =
      (factorMatrix 1 a).mulVecLin := by
    apply LinearMap.ext
    intro v
    rw [LinearEquiv.conj_apply_apply]
    change quotientCoordinates (invariantHalf.quotientRepresentation (groupGenerator a)
      (quotientCoordinates.symm v)) = _
    rw [quotientCoordinates_action, LinearEquiv.apply_symm_apply]
    rfl
  rw [h]
  exact LinearMap.toMatrix'_toLin' _

end G2DerivedPermutationFiltration.CycleModelLink
