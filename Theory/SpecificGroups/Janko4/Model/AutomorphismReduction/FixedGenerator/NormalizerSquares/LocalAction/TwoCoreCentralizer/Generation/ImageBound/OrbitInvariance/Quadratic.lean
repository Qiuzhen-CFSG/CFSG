module

public import Mathlib.Tactic.Abel
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.ImageBound.OrbitInvariance.QuadraticData

/-!
# A full-centralizer quadratic invariant on the natural homology

The checked matrix form is preserved by both original generators, hence by
all of `matrixGroup`. Its polarization pairs every a-fixed column trivially
with im(a−1), and its quadratic value vanishes on that image. It therefore
induces a well-defined binary function on ker(a−1)/im(a−1), preserved by the
entire literal involution centralizer. This function is nonconstant, and it
vanishes on the distinguished local orbit.

This proves a restriction from ambient matrix-group membership. It does not
identify the distinguished orbit with the nonzero singular locus. The saved
coordinate calculations suggest that locus contains two local orbits.

Source motivation: GLS3, Table 5.3i, printed p.270. The matrix provenance and
kernel-checked witness construction are in `QuadraticData`; that table does
not assert this homology construction or its orbit identification.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.OrbitQuadratic

/-- The ambient quadratic function, evaluated on column vectors. -/
def value (v : NaturalModule) : ZMod 2 := v ⬝ᵥ matrix *ᵥ v

attribute [local irreducible] matrix

private theorem conjugate_value (M : BinaryMatrix) (v : NaturalModule) :
    value (M *ᵥ v) = v ⬝ᵥ (Mᵀ * matrix * M) *ᵥ v := by
  rw [value, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_transpose_mulVec, dotProduct_comm]

private theorem alternating_value (T : BinaryMatrix) (v : NaturalModule) :
    v ⬝ᵥ (T + Tᵀ) *ᵥ v = 0 := by
  rw [Matrix.add_mulVec, dotProduct_add, Matrix.dotProduct_transpose_mulVec,
    CharTwo.add_self_eq_zero]

private theorem value_of_matrix_identity (M T : BinaryMatrix)
    (h : Mᵀ * matrix * M = matrix + T + Tᵀ) (v : NaturalModule) :
    value (M *ᵥ v) = value v := by
  rw [conjugate_value, h, add_assoc, Matrix.add_mulVec, dotProduct_add,
    alternating_value, add_zero]
  rfl

theorem value_matrixA (v : NaturalModule) : value (matrixA *ᵥ v) = value v := by
  obtain ⟨T, hT⟩ := a_matrix_identity
  exact value_of_matrix_identity _ T hT v

theorem value_matrixB (v : NaturalModule) : value (matrixB *ᵥ v) = value v := by
  obtain ⟨T, hT⟩ := b_matrix_identity
  exact value_of_matrix_identity _ T hT v

/-- Membership in the actual matrix group forces preservation of this form. -/
theorem value_matrixGroup (g : BinaryMatrixˣ) (hg : g ∈ matrixGroup) (v : NaturalModule) :
    value ((g : BinaryMatrix) *ᵥ v) = value v := by
  induction hg using Subgroup.closure_induction generalizing v with
  | mem g hg =>
    rcases hg with h | h
    · rw [h]; exact value_matrixA v
    · rw [h]; exact value_matrixB v
  | one => simp
  | mul g h _ _ ihg ihh =>
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ihg, ihh]
  | inv g _ ih =>
    have he := ih ((↑g⁻¹ : BinaryMatrix) *ᵥ v)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mulVec] at he
    exact he.symm

theorem value_displacement (v : NaturalModule) : value (displacement v) = 0 := by
  obtain ⟨T, hT⟩ := n_matrix_identity
  have hd : displacement v = (matrixA - 1) *ᵥ v := by
    rw [displacement_apply, Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [hd, conjugate_value, hT, alternating_value]

private def polar (u v : NaturalModule) : ZMod 2 :=
  u ⬝ᵥ matrix *ᵥ v + v ⬝ᵥ matrix *ᵥ u

private theorem value_add (u v : NaturalModule) :
    value (u + v) = value u + value v + polar u v := by
  change (u + v) ⬝ᵥ matrix *ᵥ (u + v) =
    u ⬝ᵥ matrix *ᵥ u + v ⬝ᵥ matrix *ᵥ v +
      (u ⬝ᵥ matrix *ᵥ v + v ⬝ᵥ matrix *ᵥ u)
  rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add]
  abel

private theorem polar_eq (u v : NaturalModule) :
    polar u v = value (u + v) - value u - value v := by
  rw [value_add]
  abel

private theorem polar_matrixA (u v : NaturalModule) :
    polar (matrixA *ᵥ u) (matrixA *ᵥ v) = polar u v := by
  rw [polar_eq, ← Matrix.mulVec_add, value_matrixA, value_matrixA, value_matrixA, polar_eq]

private theorem polar_displacement (u : fixedVectors) (v : NaturalModule) :
    polar (u : NaturalModule) (displacement v) = 0 := by
  have hu : matrixA *ᵥ (u : NaturalModule) = u := by
    exact sub_eq_zero.mp ((displacement_apply u).symm.trans u.property)
  have he : polar (u : NaturalModule) (matrixA *ᵥ v) = polar u v := by
    simpa only [hu] using polar_matrixA u v
  rw [displacement_apply]
  simp only [polar, Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct] at *
  rw [show
    (↑u ⬝ᵥ matrix *ᵥ matrixA *ᵥ v - ↑u ⬝ᵥ matrix *ᵥ v) +
      (matrixA *ᵥ v ⬝ᵥ matrix *ᵥ ↑u - v ⬝ᵥ matrix *ᵥ ↑u) =
      (↑u ⬝ᵥ matrix *ᵥ matrixA *ᵥ v + matrixA *ᵥ v ⬝ᵥ matrix *ᵥ ↑u) -
        (↑u ⬝ᵥ matrix *ᵥ v + v ⬝ᵥ matrix *ᵥ ↑u) by abel, he, sub_self]

theorem value_add_displacement (u : fixedVectors) (v : NaturalModule) :
    value ((u : NaturalModule) + displacement v) = value u := by
  rw [value_add, value_displacement, polar_displacement, add_zero, add_zero]

private theorem value_eq_of_sub_mem (u v : fixedVectors)
    (h : u - v ∈ displacementInFixed) : value u = value v := by
  obtain ⟨w, hw⟩ := h
  have he := value_add_displacement v w
  rw [hw] at he
  change value ((v : NaturalModule) + ((u : NaturalModule) - v)) = value v at he
  rw [add_sub_cancel] at he
  exact he

/-- The well-defined quadratic value on ker(a−1)/im(a−1). -/
def homologyValue : NaturalHomology → ZMod 2 :=
  Quotient.lift (fun v : fixedVectors => value v) (by
    intro u v h
    exact value_eq_of_sub_mem u v ((Submodule.quotientRel_def displacementInFixed).mp h))

@[simp] theorem homologyValue_mk (v : fixedVectors) :
    homologyValue (Submodule.Quotient.mk v) = value v := rfl

/-- The entire literal involution centralizer preserves the descended form. -/
theorem homologyValue_invariant (c : involutionCentralizer) (v : NaturalHomology) :
    homologyValue ((homologyAction c : Module.End (ZMod 2) NaturalHomology) v) =
      homologyValue v := by
  induction v using Submodule.Quotient.induction_on with
  | H v =>
    rw [homologyAction_mk, homologyValue_mk, homologyValue_mk]
    exact value_matrixGroup c (involutionCentralizer_le_matrixGroup c.property) v

@[simp] theorem homologyValue_zero : homologyValue 0 = 0 := by
  change value (0 : NaturalModule) = 0
  simp [value]

private def nonsingularVector : NaturalModule :=
  fun i => if (1302493977630190 : ℕ).testBit i.val then 1 else 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem nonsingularVector_fixed : displacement nonsingularVector = 0 := by
  rw [displacement_apply, sub_eq_zero]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- The descended invariant takes both binary values. -/
theorem exists_homologyValue_one : ∃ v : NaturalHomology, homologyValue v = 1 := by
  refine ⟨Submodule.Quotient.mk ⟨nonsingularVector, nonsingularVector_fixed⟩, ?_⟩
  change value nonsingularVector = 1
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem distinguishedClass_value : homologyValue distinguishedClass = 0 := by
  change value distinguishedVector = 0
  decide +kernel

theorem distinguishedOrbit_value_zero (v : NaturalHomology)
    (hv : v ∈ distinguishedOrbit) : homologyValue v = 0 := by
  obtain ⟨g, rfl⟩ := hv
  exact (homologyValue_invariant g distinguishedClass).trans distinguishedClass_value

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.OrbitQuadratic
