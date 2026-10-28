module
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.CentralField

/-!
# The geometric three-dimensional submodule of the Mathieu point stabilizer

The literal point stabilizer preserves the scalar lines in its endpoint star.
Their row span has a column annihilator of binary dimension six. Compatibility
of the certified endpoint action proves invariance under every stabilizer element;
no enumeration or unproved generator assertion is used for that step.

Small matrix identities give actual coordinates on the annihilator. The three
field columns are packed vectors 54, 93 and 407. Their companions are obtained
by the distinguished central element, which acts as omega, without inversion.
The central-field correspondence therefore gives field dimension three.

This supplies the invariant submodule for the concrete comparison needed in
James (1973), Lemma 8.3, used in Aschbacher–Smith H.12.1, printed pp.393–394.
It does not yet identify the stabilizer with SL₃(4) or split the whole module.
Matrix and endpoint data are derived from the existing ATLAS-based
`LinearNormalizer/CoreRecognition` development; its source attribution is
retained in `LinearModel/source/`. The new finite identities are kernel checked.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open CoreProjectiveAction
open scoped Matrix

/-- The column annihilator of the scalar lines in the fixed endpoint star. -/
def starAnnihilator : Submodule (ZMod 2) BinarySpace where
  carrier := {v | ∀ i : Fin 231, (1 : Fin 22) ∈ endpointPair i →
    ∀ w ∈ scalarLine (projectiveVector i), w ⬝ᵥ v = 0}
  zero_mem' := by intro i hi w hw; simp
  add_mem' := by
    intro v u hv hu i hi w hw
    rw [dotProduct_add, hv i hi w hw, hu i hi w hw, add_zero]
  smul_mem' := by
    intro a v hv i hi w hw
    rw [dotProduct_smul, hv i hi w hw, smul_zero]

lemma starAnnihilator_invariant (g : pointStabilizer) {v : BinarySpace}
    (hv : v ∈ starAnnihilator) : pointRepresentation g v ∈ starAnnihilator := by
  intro i hi w hw
  change w ⬝ᵥ (((g.val : Matrix12ˣ) : Matrix12) *ᵥ v) = 0
  rw [Matrix.dotProduct_mulVec]
  have hg : corePermutationAction g.val 1 = 1 := g.property
  have hgi : (corePermutationAction g.val)⁻¹ 1 = 1 := by
    apply (corePermutationAction g.val).injective
    simpa using hg.symm
  have hj : (1 : Fin 22) ∈ endpointPair (pairAction (corePermutationAction g.val)⁻¹ i) := by
    rw [pairAction_spec]
    exact Finset.mem_image.mpr ⟨1, hi, hgi⟩
  apply hv _ hj
  have h := corePermutationAction_spec g.val i
  rw [← h]
  exact Set.mem_image_of_mem _ hw

/-- A genuine invariant subspace of the entire literal point restriction. -/
def invariant : Subrepresentation pointRepresentation :=
  ⟨starAnnihilator, starAnnihilator_invariant⟩

/-- Interleaved binary columns for the three central-field vectors 54, 93, 407. -/
def inclusionMatrix : Matrix (Fin 12) (Fin 6) (ZMod 2) :=
  fun i j => packedVector (![54, 1077, 93, 3359, 407, 1879] j) i

/-- Binary coordinates on the invariant subspace. -/
def coordinateMatrix : Matrix (Fin 6) (Fin 12) (ZMod 2) :=
  fun i => packedVector (![3616, 3584, 576, 2048, 2816, 512] i)

private def constraints : Matrix (Fin 6) (Fin 12) (ZMod 2) :=
  fun i => packedVector (![20, 207, 263, 684, 1186, 3229] i)

private def correction : Matrix (Fin 12) (Fin 6) (ZMod 2) :=
  fun i j => packedVector (![155, 29, 151, 158, 136, 139] j) i

set_option maxRecDepth 4000 in
private lemma coordinate_inclusion : coordinateMatrix * inclusionMatrix = 1 := by
  decide +kernel

set_option maxRecDepth 4000 in
private lemma reconstruction : inclusionMatrix * coordinateMatrix + correction * constraints = 1 := by
  decide +kernel

set_option maxRecDepth 4000 in
private lemma constraint_mem (j : Fin 6) :
    let i : Fin 231 := ![3, 37, 44, 99, 161, 37] j
    (1 : Fin 22) ∈ endpointPair i ∧ constraints j ∈ scalarLine (projectiveVector i) := by
  have h : ∀ j : Fin 6, (1 : Fin 22) ∈
      endpointPair (![3, 37, 44, 99, 161, 37] j) := by decide +kernel
  refine ⟨h j, ?_⟩
  fin_cases j
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · apply Or.inr ∘ Or.inl
    decide +kernel

set_option maxRecDepth 4000 in
private lemma star_rows_vanish : ∀ i : Fin 231, (1 : Fin 22) ∈ endpointPair i →
    Matrix.vecMul (projectiveVector i) inclusionMatrix = 0 ∧
    Matrix.vecMul (Matrix.vecMul (projectiveVector i) matrixJ) inclusionMatrix = 0 := by
  decide +kernel

lemma inclusion_mem (v : Fin 6 → ZMod 2) : inclusionMatrix *ᵥ v ∈ starAnnihilator := by
  intro i hi w hw
  obtain ⟨h₁,h₂⟩ := star_rows_vanish i hi
  rcases hw with rfl | rfl | rfl
  · rw [Matrix.dotProduct_mulVec, h₁, zero_dotProduct]
  · rw [Matrix.dotProduct_mulVec, h₂, zero_dotProduct]
  · rw [add_dotProduct, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec,
      h₁, h₂, zero_dotProduct, add_zero]

lemma inclusion_coordinates {v : BinarySpace} (hv : v ∈ starAnnihilator) :
    inclusionMatrix *ᵥ (coordinateMatrix *ᵥ v) = v := by
  have hc : constraints *ᵥ v = 0 := by
    funext j
    exact hv _ (constraint_mem j).1 _ (constraint_mem j).2
  calc
    _ = inclusionMatrix *ᵥ (coordinateMatrix *ᵥ v) + correction *ᵥ (constraints *ᵥ v) := by
      rw [hc, Matrix.mulVec_zero, add_zero]
    _ = (inclusionMatrix * coordinateMatrix + correction * constraints) *ᵥ v := by
      rw [Matrix.add_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    _ = v := by rw [reconstruction, Matrix.one_mulVec]

/-- Actual binary coordinates, including an inverse, on the geometric subspace. -/
def invariantBinaryEquiv : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] invariant.toSubmodule :=
  { inclusionMatrix.mulVecLin.codRestrict starAnnihilator inclusion_mem with
    invFun := fun v => coordinateMatrix *ᵥ v.val
    left_inv := fun v => by
      change coordinateMatrix *ᵥ (inclusionMatrix *ᵥ v) = v
      rw [Matrix.mulVec_mulVec, coordinate_inclusion, Matrix.one_mulVec]
    right_inv := fun v => Subtype.ext (inclusion_coordinates v.property) }

lemma invariant_finrank : Module.finrank (ZMod 2) invariant.toSubmodule = 6 := by
  rw [← invariantBinaryEquiv.finrank_eq]
  simp

lemma invariant_ne_bot : invariant ≠ ⊥ := by
  intro h
  have hd := invariant_finrank
  rw [h] at hd
  change Module.finrank (ZMod 2) (⊥ : Submodule (ZMod 2) BinarySpace) = 6 at hd
  simp at hd

lemma invariant_ne_top : invariant ≠ ⊤ := by
  intro h
  have hd := invariant_finrank
  rw [h] at hd
  change Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) BinarySpace) = 6 at hd
  simp at hd

/-- Binary coordinates of three quadratic-field entries, with the actual central root. -/
def flatten : (Fin 3 → F) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2) where
  toFun v := ![(v 0).re, (v 0).im, (v 1).re, (v 1).im, (v 2).re, (v 2).im]
  invFun v := ![⟨v 0, v 1⟩, ⟨v 2, v 3⟩, ⟨v 4, v 5⟩]
  left_inv v := by funext i; fin_cases i <;> rfl
  right_inv v := by funext i; fin_cases i <;> rfl
  map_add' v w := by funext i; fin_cases i <;> rfl
  map_smul' a v := by funext i; fin_cases i <;> rfl

/-- Specified coordinates on the invariant binary subspace. -/
def invariantCoordinates : (Fin 3 → F) ≃ₗ[ZMod 2] invariant.toSubmodule :=
  flatten.trans invariantBinaryEquiv

/-- The three central-field columns used to fix the later SL₃ comparison. -/
def naturalInclusion : (Fin 3 → F) →ₗ[ZMod 2] BinarySpace :=
  invariant.toSubmodule.subtype.comp invariantCoordinates.toLinearMap

lemma naturalInclusion_apply (v : Fin 3 → F) :
    naturalInclusion v = inclusionMatrix *ᵥ flatten v := rfl

lemma naturalInclusion_injective : Function.Injective naturalInclusion :=
  invariant.toSubmodule.subtype_injective.comp invariantCoordinates.injective

lemma naturalInclusion_range : LinearMap.range naturalInclusion = starAnnihilator := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    exact (invariantCoordinates w).property
  · intro hv
    obtain ⟨w, hw⟩ := invariantCoordinates.surjective ⟨v, hv⟩
    exact ⟨w, congrArg Subtype.val hw⟩

private def omegaMatrix : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  fun i j => if (![2, 3, 8, 12, 32, 48] i : ℕ).testBit j.val then 1 else 0

private lemma inclusion_scalar_matrix :
    (1 + matrixJ) * inclusionMatrix = inclusionMatrix * omegaMatrix := by decide +kernel

private lemma flatten_omega (v : Fin 3 → F) :
    flatten ((QuadraticAlgebra.omega : F) • v) = omegaMatrix *ᵥ flatten v := by
  revert v
  simp only [funext_iff]
  decide +kernel

/-- These coordinates retain the specified central element, without inverting it. -/
lemma naturalInclusion_scalar (v : Fin 3 → F) :
    naturalInclusion ((QuadraticAlgebra.omega : F) • v) =
      pointRepresentation pointScalar (naturalInclusion v) := by
  rw [naturalInclusion_apply, flatten_omega, Matrix.mulVec_mulVec]
  change _ = (scalarUnit : Matrix12) *ᵥ (inclusionMatrix *ᵥ flatten v)
  rw [Matrix.mulVec_mulVec, coe_scalarUnit, inclusion_scalar_matrix]

/-- The same geometric invariant subspace over the field forced by the center. -/
def invariantField : letI := fieldModule binaryRepresentation binaryRepresentation_faithful
    Subrepresentation (pointFieldRepresentation binaryRepresentation binaryRepresentation_faithful) :=
  pointSubrepresentationEquiv binaryRepresentation binaryRepresentation_faithful invariant

lemma invariantField_finrank :
    letI := fieldModule binaryRepresentation binaryRepresentation_faithful
    Module.finrank F invariantField.toSubmodule = 3 := by
  let := fieldModule binaryRepresentation binaryRepresentation_faithful
  have h := pointSubrepresentation_finrank binaryRepresentation binaryRepresentation_faithful invariant
  rw [invariant_finrank] at h
  change 2 * Module.finrank F invariantField.toSubmodule = 6 at h
  omega

end Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel
