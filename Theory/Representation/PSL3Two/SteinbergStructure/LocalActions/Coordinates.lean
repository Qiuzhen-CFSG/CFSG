module

public import Theory.Representation.PSL3Two.IrreducibleCatalogue.Coordinates
public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups.Coordinates
import Mathlib.Tactic.FinCases

/-!
# Concrete local calculations on the binary Steinberg module

The upper triangular subgroup fixes exactly zero and the matrix unit E₀₂;
the latter has precisely that group stabilizer. For each marked parabolic,
eight explicit action differences give the standard basis of the trace-zero
endomorphisms. All finite certificates use the actual conjugation action,
through its proved eight-coordinate equivalence, and are checked by the kernel.

Source: Aschbacher–Smith H.6.3(4–5), printed pp.387–388, combined manuscript
of 1 March 2004. The group stabilizer follows the source proof's C_L(m),
correcting the C_M(m) typo in the printed statement.
-/

open Matrix Representation
open BinaryLinearThree.IrreducibleCatalogue
open Matrix.PSL3Two
namespace BinaryLinearThree.SteinbergStructure.LocalActions
public noncomputable section

private def act (g : Group) (v : Eight) : Eight :=
  readMatrix (g.val * matrixOf v * g.val.adjugate)

private theorem coordinates_sub (u v : Steinberg) :
    coordinates (u - v) = coordinates u - coordinates v := coordinates.map_sub u v

private theorem coordinates_action (g : Group) (v : Eight) :
    coordinates (S g (coordinates.symm v)) = act g v := by
  change readMatrix (LinearMap.toMatrix' (W g ∘ₗ (matrixOf v).toLin' ∘ₗ W g⁻¹)) = _
  change readMatrix (LinearMap.toMatrix'
    (g.val.toLin' ∘ₗ (matrixOf v).toLin' ∘ₗ g.val.adjugate.toLin')) = _
  rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul, LinearMap.toMatrix'_toLin']
  exact congrArg readMatrix (Matrix.mul_assoc _ _ _).symm

/-- The trace-zero matrix unit E₀₂, expressed in the literal adjoint space. -/
def rootVector : Steinberg := coordinates.symm (Pi.single 1 1)

private def upper12 : Group := ⟨!![1,0,0;0,1,1;0,0,1], by decide⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem stabilizer_certificate : ∀ g : Group,
    act g (Pi.single 1 1) = Pi.single 1 1 ↔ g ∈ borelSL := by
  simp only [act, Matrix.adjugate_fin_three, mem_borelSL_iff]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem fixed_certificate : ∀ v : Eight,
    act IrreducibleCatalogue.shear v = v → act upper12 v = v →
      v = 0 ∨ v = Pi.single 1 1 := by
  simp only [act, Matrix.adjugate_fin_three]
  decide +kernel

/-- The marked vector is nonzero. -/
theorem rootVector_ne_zero : rootVector ≠ 0 := by
  intro he
  have h := congrArg (fun v => coordinates v 1) he
  simp [rootVector] at h

/-- The full group stabilizer of E₀₂ is precisely the upper triangular subgroup. -/
theorem rootVector_stabilizer (g : Group) : S g rootVector = rootVector ↔ g ∈ borelSL := by
  rw [← coordinates.injective.eq_iff]
  simpa only [rootVector, coordinates_action, LinearEquiv.apply_symm_apply] using
    stabilizer_certificate g

/-- The Borel fixes exactly the zero vector and E₀₂. -/
theorem borel_fixed_iff (v : Steinberg) :
    (∀ g ∈ borelSL, S g v = v) ↔ v = 0 ∨ v = rootVector := by
  constructor
  · intro h
    have hc (g : Group) (hg : g ∈ borelSL) : act g (coordinates v) = coordinates v := by
      rw [← coordinates_action, LinearEquiv.symm_apply_apply, h g hg]
    have h1 : IrreducibleCatalogue.shear ∈ borelSL := by decide
    have h2 : upper12 ∈ borelSL := by decide
    rcases fixed_certificate (coordinates v) (hc _ h1) (hc _ h2) with hz | hr
    · left
      exact coordinates.injective (by simpa using hz)
    · right
      exact coordinates.injective (by simpa [rootVector] using hr)
  · rintro (rfl | rfl) g hg
    · exact map_zero _
    · exact (rootVector_stabilizer g).mpr hg

-- Each table entry is an actual parabolic element, followed by its displacement seed.
private def pointActor (i : Fin 8) : Group :=
  ![⟨!![1,0,0;0,1,0;0,1,1], by decide⟩,
    upper12, upper12, upper12,
    ⟨!![1,0,0;0,1,0;0,1,1], by decide⟩,
    ⟨!![1,0,0;0,1,0;0,1,1], by decide⟩,
    ⟨!![1,0,1;0,1,0;0,0,1], by decide⟩,
    ⟨!![1,0,0;0,1,0;0,1,1], by decide⟩] i

private def pointSeed (i : Fin 8) : Eight :=
  ![![0,1,0,0,0,0,0,0], ![1,0,0,0,0,0,0,0],
    ![0,0,0,0,1,0,0,0], ![0,0,0,0,0,0,1,0],
    ![0,0,1,0,0,0,0,0], ![0,0,0,0,0,0,1,0],
    ![0,0,0,0,1,0,0,1], ![0,0,0,1,0,0,1,0]] i

private def lineActor (i : Fin 8) : Group :=
  ![⟨!![1,0,1;0,1,0;0,0,1], by decide⟩,
    upper12, upper12, upper12,
    ⟨!![1,0,0;1,1,0;0,0,1], by decide⟩,
    IrreducibleCatalogue.shear,
    ⟨!![1,0,1;0,1,0;0,0,1], by decide⟩, upper12] i

private def lineSeed (i : Fin 8) : Eight :=
  ![![0,0,0,0,0,1,0,0], ![1,0,0,0,0,0,0,0],
    ![0,0,0,0,1,0,0,0], ![0,0,0,0,0,0,1,0],
    ![0,0,0,0,0,1,0,0], ![0,0,0,0,1,0,0,0],
    ![0,0,0,0,1,0,0,1], ![0,0,0,0,0,1,1,0]] i

private theorem pointActor_mem (i : Fin 8) : pointActor i ∈ pointParabolicSL := by
  fin_cases i <;> decide

private theorem lineActor_mem (i : Fin 8) : lineActor i ∈ lineParabolicSL := by
  fin_cases i <;> decide

private theorem point_displacement (i : Fin 8) :
    act (pointActor i) (pointSeed i) - pointSeed i = Pi.single i 1 := by
  simp only [act, Matrix.adjugate_fin_three]
  fin_cases i <;> decide

private theorem line_displacement (i : Fin 8) :
    act (lineActor i) (lineSeed i) - lineSeed i = Pi.single i 1 := by
  simp only [act, Matrix.adjugate_fin_three]
  fin_cases i <;> decide

/-- Every adjoint coordinate basis vector is an actual point-parabolic displacement. -/
theorem point_basis_displacement (i : Fin 8) :
    ∃ g ∈ pointParabolicSL, ∃ v : Steinberg,
      S g v - v = coordinates.symm (Pi.single i 1) := by
  refine ⟨pointActor i, pointActor_mem i, coordinates.symm (pointSeed i), ?_⟩
  apply coordinates.injective
  rw [coordinates_sub, coordinates_action, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]
  exact point_displacement i

/-- Every adjoint coordinate basis vector is an actual line-parabolic displacement. -/
theorem line_basis_displacement (i : Fin 8) :
    ∃ g ∈ lineParabolicSL, ∃ v : Steinberg,
      S g v - v = coordinates.symm (Pi.single i 1) := by
  refine ⟨lineActor i, lineActor_mem i, coordinates.symm (lineSeed i), ?_⟩
  apply coordinates.injective
  rw [coordinates_sub, coordinates_action, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]
  exact line_displacement i

end
end BinaryLinearThree.SteinbergStructure.LocalActions
