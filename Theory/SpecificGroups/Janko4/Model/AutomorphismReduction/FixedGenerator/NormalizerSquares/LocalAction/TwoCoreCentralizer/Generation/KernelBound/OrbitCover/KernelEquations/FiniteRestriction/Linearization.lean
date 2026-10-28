module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.ExteriorSpace
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.InvariantForm

/-!
# Radical-space restrictions from the natural homology kernel

Write `N = A - 1`, `I = im N`, and `K = ker N` in the literal column module.
An exterior-space stabilizer commuting with `A` preserves the exterior forms
whose radicals contain `I` or `K`. If its action on `K/I` is trivial, then for
`R` annihilating `I` and `u ∈ K`, pullback satisfies
`(gᵀ R g)(u,v) = R(u,gv)`. This removes one occurrence of the unknown matrix
from the mixed evaluations and gives necessary linear restrictions on it.
The restrictions hold for the inverse as well. The ambient bilinear invariant
also gives the displacement-pairing identity needed for a coordinate reduction.

These are restrictions on arbitrary matrix units under the displayed hypotheses.
They assert neither the coordinate equations nor identification of the exterior
stabilizer with the matrix group. The finite chart theorem requires further work.
Matrix provenance and exterior-space motivation: `../source/README.md` and
`Janko4/Model/Data.lean`. The coordinate target is defined in
`OrbitCover/Coordinates.lean`.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates

/-- Bilinear evaluation in the unchanged natural column basis. -/
def formValue (R : BinaryMatrix) (u v : NaturalModule) : ZMod 2 := u ⬝ᵥ R *ᵥ v

theorem formValue_pullback (g : BinaryMatrixˣ) (R : BinaryMatrix)
    (u v : NaturalModule) :
    formValue (formPullback g R) u v =
      formValue R ((g : BinaryMatrix) *ᵥ u) ((g : BinaryMatrix) *ᵥ v) := by
  simp only [formValue, formPullback, ← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- Exterior forms whose left radical contains a specified subspace. -/
def exteriorRadical (U : Submodule (ZMod 2) NaturalModule) :
    Submodule (ZMod 2) BinaryMatrix where
  carrier := {R | R ∈ exteriorFormSpace ∧ ∀ u ∈ U, ∀ v, formValue R u v = 0}
  zero_mem' := by simp [formValue]
  add_mem' := by
    rintro R S ⟨hR, hRU⟩ ⟨hS, hSU⟩
    refine ⟨exteriorFormSpace.add_mem hR hS, ?_⟩
    intro u hu v
    simp only [formValue, Matrix.add_mulVec, dotProduct_add]
    change formValue R u v + formValue S u v = 0
    rw [hRU u hu v, hSU u hu v, add_zero]
  smul_mem' := by
    rintro c R ⟨hR, hRU⟩
    refine ⟨exteriorFormSpace.smul_mem c hR, ?_⟩
    intro u hu v
    simp only [formValue, Matrix.smul_mulVec, dotProduct_smul]
    change c • formValue R u v = 0
    rw [hRU u hu v, smul_zero]

/-- Pullback preserves the radical condition whenever the matrix preserves the
specified vector subspace. -/
theorem formPullback_mem_exteriorRadical (g : BinaryMatrixˣ)
    (hext : g ∈ formStabilizer exteriorFormSpace)
    (U : Submodule (ZMod 2) NaturalModule)
    (hU : ∀ u ∈ U, (g : BinaryMatrix) *ᵥ u ∈ U)
    {R : BinaryMatrix} (hR : R ∈ exteriorRadical U) :
    formPullback g R ∈ exteriorRadical U := by
  refine ⟨(hext R).mpr hR.1, ?_⟩
  intro u hu v
  rw [formValue_pullback]
  exact hR.2 _ (hU u hu) _

theorem kernelConditions_displacement (g : BinaryMatrixˣ) (hker : KernelConditions g)
    (v : NaturalModule) :
    (g : BinaryMatrix) *ᵥ displacement v = displacement ((g : BinaryMatrix) *ᵥ v) := by
  simp only [displacement_apply, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hker.1]

theorem kernelConditions_preserves_displacementVectors (g : BinaryMatrixˣ)
    (hker : KernelConditions g) {v : NaturalModule} (hv : v ∈ displacementVectors) :
    (g : BinaryMatrix) *ᵥ v ∈ displacementVectors := by
  obtain ⟨u, rfl⟩ := hv
  exact ⟨(g : BinaryMatrix) *ᵥ u, (kernelConditions_displacement g hker u).symm⟩

theorem kernelConditions_preserves_fixedVectors (g : BinaryMatrixˣ)
    (hker : KernelConditions g) {v : NaturalModule} (hv : v ∈ fixedVectors) :
    (g : BinaryMatrix) *ᵥ v ∈ fixedVectors := by
  change displacement ((g : BinaryMatrix) *ᵥ v) = 0
  rw [← kernelConditions_displacement g hker]
  change (g : BinaryMatrix) *ᵥ displacement v = 0
  rw [show displacement v = 0 from hv, Matrix.mulVec_zero]

/-- The homology condition makes pullback on the mixed fixed-vector evaluations
linear in the matrix entries. The contribution of `g u - u` vanishes in the
radical, so only the second argument is transformed. -/
theorem formValue_pullback_fixed_left (g : BinaryMatrixˣ) (hker : KernelConditions g)
    {R : BinaryMatrix} (hR : R ∈ exteriorRadical displacementVectors)
    {u : NaturalModule} (hu : u ∈ fixedVectors) (v : NaturalModule) :
    formValue (formPullback g R) u v = formValue R u ((g : BinaryMatrix) *ᵥ v) := by
  have hfix : matrixA *ᵥ u = u := sub_eq_zero.mp ((displacement_apply u).symm.trans hu)
  obtain ⟨w, hw⟩ := hker.2 u hfix
  have hd : (g : BinaryMatrix) *ᵥ u - u ∈ displacementVectors :=
    ⟨w, (hw.trans (displacement_apply w).symm).symm⟩
  have he := hR.2 _ hd ((g : BinaryMatrix) *ᵥ v)
  rw [formValue_pullback]
  exact sub_eq_zero.mp (by simpa only [formValue, sub_dotProduct] using he)

/-- A necessary linear restriction, with the original explicit exterior space
retained: every mixed row of `R g` comes from a form with the same radical. -/
def MixedFormConditions (g : BinaryMatrixˣ) : Prop :=
  ∀ R ∈ exteriorRadical displacementVectors,
    ∃ S ∈ exteriorRadical displacementVectors,
      ∀ u ∈ fixedVectors, ∀ v,
        formValue S u v = formValue R u ((g : BinaryMatrix) *ᵥ v)

theorem mixedFormConditions_of_kernel (g : BinaryMatrixˣ) (hker : KernelConditions g)
    (hext : g ∈ formStabilizer exteriorFormSpace) : MixedFormConditions g := by
  intro R hR
  refine ⟨formPullback g R, formPullback_mem_exteriorRadical g hext _ ?_ hR, ?_⟩
  · intro u hu
    exact kernelConditions_preserves_displacementVectors g hker hu
  · intro u hu v
    exact formValue_pullback_fixed_left g hker hR hu v

/-- The literal natural-homology condition is closed under inversion. -/
theorem kernelConditions_inv (g : BinaryMatrixˣ) (hker : KernelConditions g) :
    KernelConditions g⁻¹ := by
  have hc : (g⁻¹ : BinaryMatrixˣ).val * matrixA = matrixA * (g⁻¹ : BinaryMatrixˣ).val :=
    (show Commute (g : BinaryMatrix) matrixA from hker.1).units_inv_left.eq
  refine ⟨hc, ?_⟩
  intro v hv
  have hfix : matrixA *ᵥ ((g⁻¹ : BinaryMatrixˣ) : BinaryMatrix) *ᵥ v =
      ((g⁻¹ : BinaryMatrixˣ) : BinaryMatrix) *ᵥ v := by
    rw [Matrix.mulVec_mulVec, ← hc, ← Matrix.mulVec_mulVec, hv]
  obtain ⟨w, hw⟩ := hker.2 _ hfix
  have hw' : v - ((g⁻¹ : BinaryMatrixˣ) : BinaryMatrix) *ᵥ v = displacement w := by
    simpa only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec,
      displacement_apply] using hw
  refine ⟨-w, ?_⟩
  rw [← displacement_apply, map_neg, ← hw', neg_sub]

theorem mixedFormConditions_inv_of_kernel (g : BinaryMatrixˣ)
    (hker : KernelConditions g) (hext : g ∈ formStabilizer exteriorFormSpace) :
    MixedFormConditions g⁻¹ :=
  mixedFormConditions_of_kernel g⁻¹ (kernelConditions_inv g hker)
    ((formStabilizer exteriorFormSpace).inv_mem hext)

/-- Every element of the published exterior span is symmetric in characteristic
two; this follows from the decoded alternating generators. -/
theorem exteriorFormSpace_transpose {R : BinaryMatrix} (hR : R ∈ exteriorFormSpace) :
    Rᵀ = R := by
  change R ∈ Submodule.span (ZMod 2) (Set.range exteriorBasisForm) at hR
  induction hR using Submodule.span_induction with
  | mem R hR =>
    obtain ⟨i, rfl⟩ := hR
    exact decodeExteriorForm_transpose _
  | zero => exact Matrix.transpose_zero
  | add R S _ _ hR hS => simp only [Matrix.transpose_add, hR, hS]
  | smul r R _ hR => simp only [Matrix.transpose_smul, hR]

theorem formValue_symm {R : BinaryMatrix} (hR : R ∈ exteriorFormSpace)
    (u v : NaturalModule) : formValue R u v = formValue R v u := by
  dsimp only [formValue]
  simpa only [exteriorFormSpace_transpose hR] using
    (Matrix.dotProduct_transpose_mulVec R u v)

/-- On two fixed vectors the homology condition makes pullback of a form
annihilating displacements pointwise trivial. -/
theorem formValue_pullback_fixed (g : BinaryMatrixˣ) (hker : KernelConditions g)
    {R : BinaryMatrix} (hR : R ∈ exteriorRadical displacementVectors)
    {u v : NaturalModule} (hu : u ∈ fixedVectors) (hv : v ∈ fixedVectors) :
    formValue (formPullback g R) u v = formValue R u v := by
  rw [formValue_pullback_fixed_left g hker hR hu, formValue_symm hR.1]
  have hfix : matrixA *ᵥ v = v := sub_eq_zero.mp ((displacement_apply v).symm.trans hv)
  obtain ⟨w, hw⟩ := hker.2 v hfix
  have hd : (g : BinaryMatrix) *ᵥ v - v ∈ displacementVectors :=
    ⟨w, (hw.trans (displacement_apply w).symm).symm⟩
  have he := hR.2 _ hd u
  have he' : formValue R ((g : BinaryMatrix) *ᵥ v) u = formValue R v u :=
    sub_eq_zero.mp (by simpa only [formValue, sub_dotProduct] using he)
  exact he'.trans (formValue_symm hR.1 v u)

theorem mem_formStabilizer_exteriorRadical (g : BinaryMatrixˣ)
    (hext : g ∈ formStabilizer exteriorFormSpace)
    (U : Submodule (ZMod 2) NaturalModule)
    (hU : ∀ u ∈ U, (g : BinaryMatrix) *ᵥ u ∈ U)
    (hUi : ∀ u ∈ U, ((g⁻¹ : BinaryMatrixˣ) : BinaryMatrix) *ᵥ u ∈ U) :
    g ∈ formStabilizer (exteriorRadical U) := by
  intro R
  constructor
  · intro hR
    have hi := formPullback_mem_exteriorRadical g⁻¹
      ((formStabilizer exteriorFormSpace).inv_mem hext) U hUi hR
    simpa only [← formPullback_mul, mul_inv_cancel, formPullback_one] using hi
  · exact formPullback_mem_exteriorRadical g hext U hU

/-- Both intrinsic radical spaces are setwise preserved under the exact task
hypotheses. Their smaller finite descriptions can therefore be certified
independently of the final vector restriction. -/
theorem kernelConditions_preserves_radicals (g : BinaryMatrixˣ)
    (hker : KernelConditions g) (hext : g ∈ formStabilizer exteriorFormSpace) :
    g ∈ formStabilizer (exteriorRadical displacementVectors) ∧
      g ∈ formStabilizer (exteriorRadical fixedVectors) := by
  have hi := kernelConditions_inv g hker
  constructor
  · exact mem_formStabilizer_exteriorRadical g hext displacementVectors
      (fun _ hu => kernelConditions_preserves_displacementVectors g hker hu)
      (fun _ hu => kernelConditions_preserves_displacementVectors g⁻¹ hi hu)
  · exact mem_formStabilizer_exteriorRadical g hext fixedVectors
      (fun _ hu => kernelConditions_preserves_fixedVectors g hker hu)
      (fun _ hu => kernelConditions_preserves_fixedVectors g⁻¹ hi hu)

/-- Preservation of the ambient form descends to its displacement pairing.
This is the coordinate-free identity behind the induced form on the
50-dimensional displacement space; no dimension or nondegeneracy is assumed. -/
theorem formValue_displacement_invariant (g : BinaryMatrixˣ) (hker : KernelConditions g)
    (hform : formPullback g invariantForm = invariantForm) (u v : NaturalModule) :
    formValue invariantForm ((g : BinaryMatrix) *ᵥ u)
        (displacement ((g : BinaryMatrix) *ᵥ v)) =
      formValue invariantForm u (displacement v) := by
  rw [← kernelConditions_displacement g hker, ← formValue_pullback, hform]

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates
