module

public import Theory.Representation.G2DerivedPermutationFiltration.CycleFiltration.ModelLink.BoundaryData
/-!
# Coordinates on the actual binary G₂ incidence kernel

The literal flag enumeration identifies the two endpoint pushforwards with
both blocks of the checked numerical boundary. Restricting this equivalence
to kernels and using the certified cycle basis gives 64 coordinates on the
actual incidence kernel. The two actual derived-group generators act by the
saved cycle matrices, with the inverse-word convention from `CosetAction`.

Source application: Aschbacher–Smith G.7.2(3), printed pp.347–348.
-/

@[expose] public section

open G2DerivedPermutationFiltration G2DerivedPermutationFiltration.CycleData
open G2DerivedPermutationFiltration.CycleData.Certificate
open G2DerivedPermutationFiltration.CycleFlagCoordinates
open G2DerivedPermutationFiltration.VertexCoordinates
namespace G2DerivedPermutationFiltration.CycleModelLink
lemma actual_boundary_zero (v : BinaryPermutation.Full Flag)
    (hv : v ∈ cycleSubrepresentation) : boundaryMatrix.mulVec (flagCoordinates v) = 0 := by
  have h := (mem_cycleSubrepresentation v).mp hv
  have h0 (r : Fin 63) := pushEval 0 (flagCoordinates v) r
  have h1 (r : Fin 63) := pushEval 1 (flagCoordinates v) r
  simp only [LinearEquiv.symm_apply_apply, h.1, h.2, Pi.zero_apply, endpoint_eq] at h0 h1
  funext j
  refine Fin.addCases (m := 63) (n := 63) ?_ ?_ j
  · intro r
    rw [boundaryRow0]
    exact (h0 r).symm
  · intro r
    rw [boundaryRow1]
    exact (h1 r).symm

lemma numerical_cycle_mem (v : Certificate.Flags) (hv : boundaryMatrix.mulVec v = 0) :
    flagCoordinates.symm v ∈ cycleSubrepresentation := by
  rw [mem_cycleSubrepresentation]
  have hz0 (r : Fin 63) := congrFun hv (Fin.castAdd 63 r)
  have hz1 (r : Fin 63) := congrFun hv (Fin.natAdd 63 r)
  simp only [boundaryRow0, Pi.zero_apply] at hz0
  simp only [boundaryRow1, Pi.zero_apply] at hz1
  constructor
  · funext q
    obtain ⟨r, rfl⟩ := (vertex_bijective 0).surjective q
    rw [pushEval]
    simpa only [endpoint_eq, Pi.zero_apply] using hz0 r
  · funext q
    obtain ⟨r, rfl⟩ := (vertex_bijective 1).surjective q
    rw [pushEval]
    simpa only [endpoint_eq, Pi.zero_apply] using hz1 r

noncomputable def kernelEquiv :
    cycleSubrepresentation.toSubmodule ≃ₗ[ZMod 2] cycleKernel where
  toFun v := ⟨flagCoordinates v.val, actual_boundary_zero v.val v.property⟩
  invFun v := ⟨flagCoordinates.symm v.val, numerical_cycle_mem v.val v.property⟩
  map_add' v w := Subtype.ext (map_add flagCoordinates v.val w.val)
  map_smul' a v := Subtype.ext (map_smul flagCoordinates a v.val)
  left_inv v := Subtype.ext (flagCoordinates.symm_apply_apply v.val)
  right_inv v := Subtype.ext (flagCoordinates.apply_symm_apply v.val)

noncomputable def coordinates : cycleSubrepresentation.toSubmodule ≃ₗ[ZMod 2] Certificate.Space :=
  kernelEquiv.trans Certificate.cycleCoordinates

set_option maxRecDepth 8192 in
theorem coordinates_symm_val (v : Certificate.Space) :
    (coordinates.symm v).val = cycleLift v := rfl

theorem actionMatrix_eq (a : Fin 2) : actionMatrix a = derivedCycleMatrix a := rfl

theorem coordinates_action (a : Fin 2) (v : cycleSubrepresentation.toSubmodule) :
    coordinates (cycleSubrepresentation.toRepresentation (groupGenerator a) v) =
      (actionMatrix a).mulVec (coordinates v) := by
  apply coordinates.symm.injective
  apply Subtype.ext
  rw [LinearEquiv.symm_apply_apply, coordinates_symm_val, actionMatrix_eq, cycleLift_derived]
  have hv : cycleLift (coordinates v) = v.val :=
    (coordinates_symm_val (coordinates v)).symm.trans
      (congrArg Subtype.val (coordinates.symm_apply_apply v))
  rw [hv]
  rfl

end G2DerivedPermutationFiltration.CycleModelLink
