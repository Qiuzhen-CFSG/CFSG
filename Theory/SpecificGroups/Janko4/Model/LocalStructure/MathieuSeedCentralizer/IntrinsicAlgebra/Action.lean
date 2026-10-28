module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.Defs
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.ExteriorInvariance

/-!
# The full seed centralizer acts on its intrinsic spaces

Membership in the actual generated matrix group supplies preservation of the
original exterior space and invariant form. Commutation with the literal seed
then gives the actions on its displacement kernel and on `radicalForms`.
The latter is a left action by **inverse** pullback, so it is a homomorphism.
No rank, basis, centralizer generation or local-subgroup assumption is used.

Source: the explicit ambient generator certificates in `ExteriorInvariance`
and `InvariantForm`, with the intrinsic construction described in `Defs`.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra

open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates

theorem matrixGroup_le_ambientFormsStabilizer : matrixGroup ≤ formStabilizer ambientForms :=
  matrixGroup_le_formStabilizer exteriorFormSpace
    matrixUnitA_mem_exteriorFormStabilizer
    matrixUnitB_mem_exteriorFormStabilizer

theorem model_preserves_ambientForms (g : Model) (R : BinaryMatrix) :
    formPullback (toAmbient g) R ∈ ambientForms ↔ R ∈ ambientForms :=
  matrixGroup_le_ambientFormsStabilizer g.property R

theorem model_preserves_invariantForm (g : Model) :
    formPullback (toAmbient g) invariantForm = invariantForm :=
  matrixGroup_preserves_invariantForm g.property

def centralizerUnit : centralizer →* BinaryMatrixˣ := toAmbient.comp centralizer.subtype

def columnRepresentation : Representation (ZMod 2) centralizer Column :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp
    ((Units.coeHom BinaryMatrix).comp centralizerUnit)

set_option maxRecDepth 2048 in
theorem columnRepresentation_apply (c : centralizer) (v : Column) :
    columnRepresentation c v = (centralizerUnit c : BinaryMatrix) *ᵥ v := rfl

theorem centralizer_commutes_seed (c : centralizer) :
    seed * (c : Model) = (c : Model) * seed :=
  c.property seed (Set.mem_singleton seed)

theorem centralizer_commutes_displacement (c : centralizer) :
    displacementMatrix * (centralizerUnit c : BinaryMatrix) =
      (centralizerUnit c : BinaryMatrix) * displacementMatrix := by
  have h := congrArg toMatrix (centralizer_commutes_seed c)
  change toMatrix (seed * (c : Model)) = toMatrix ((c : Model) * seed) at h
  simp only [map_mul] at h
  change (toMatrix seed - 1) * toMatrix (c : Model) =
    toMatrix (c : Model) * (toMatrix seed - 1)
  rw [sub_mul, mul_sub, one_mul, mul_one, h]

theorem mulVec_mem_kernelSpace (c : centralizer) {v : Column} (hv : v ∈ kernelSpace) :
    (centralizerUnit c : BinaryMatrix) *ᵥ v ∈ kernelSpace := by
  change displacementMatrix *ᵥ ((centralizerUnit c : BinaryMatrix) *ᵥ v) = 0
  rw [Matrix.mulVec_mulVec, centralizer_commutes_displacement, ← Matrix.mulVec_mulVec,
    (mem_kernelSpace v).mp hv, Matrix.mulVec_zero]

theorem kernelSpace_invariant (c : centralizer) :
    kernelSpace ≤ kernelSpace.comap (columnRepresentation c) := by
  intro v hv
  rw [Submodule.mem_comap, columnRepresentation_apply]
  exact mulVec_mem_kernelSpace c hv

/-- Restriction of the column action to the actual displacement kernel. -/
def kernelRepresentation : Representation (ZMod 2) centralizer kernelSpace :=
  columnRepresentation.subrepresentation kernelSpace kernelSpace_invariant

def kernelAction : centralizer →* (Module.End (ZMod 2) kernelSpace)ˣ :=
  kernelRepresentation.asGroupHom

set_option maxRecDepth 2048 in
theorem kernelAction_apply (c : centralizer) (v : kernelSpace) :
    ((kernelAction c : Module.End (ZMod 2) kernelSpace) v : Column) =
      (centralizerUnit c : BinaryMatrix) *ᵥ (v : Column) := rfl

theorem pullback_mem_radicalForms (c : centralizer) {R : BinaryMatrix}
    (hR : R ∈ radicalForms) : formPullback (centralizerUnit c) R ∈ radicalForms := by
  refine ⟨(model_preserves_ambientForms c R).mpr hR.1, ?_⟩
  intro v hv
  have hg := mulVec_mem_kernelSpace c hv
  simp only [formPullback, ← Matrix.mulVec_mulVec, hR.2 _ hg, Matrix.mulVec_zero]

/-- The inverse in this definition converts pullback into a left action. -/
def formRepresentation : Representation (ZMod 2) centralizer BinaryMatrix where
  toFun c :=
    { toFun := formPullback (centralizerUnit c)⁻¹
      map_add' := by intro R S; simp [formPullback, Matrix.mul_add, Matrix.add_mul]
      map_smul' := by intro a R; simp [formPullback] }
  map_one' := by
    ext R i j
    simp [formPullback]
  map_mul' := by
    intro c d
    ext R i j
    change formPullback (centralizerUnit (c * d))⁻¹ R i j =
      formPullback (centralizerUnit c)⁻¹ (formPullback (centralizerUnit d)⁻¹ R) i j
    rw [map_mul, mul_inv_rev, formPullback_mul]

theorem formRepresentation_apply (c : centralizer) (R : BinaryMatrix) :
    formRepresentation c R = formPullback (centralizerUnit c)⁻¹ R := rfl

theorem radicalForms_invariant (c : centralizer) :
    radicalForms ≤ radicalForms.comap (formRepresentation c) := by
  intro R hR
  simpa only [Submodule.mem_comap, formRepresentation_apply, map_inv] using
    pullback_mem_radicalForms c⁻¹ hR

def radicalRepresentation : Representation (ZMod 2) centralizer radicalForms :=
  formRepresentation.subrepresentation radicalForms radicalForms_invariant

/-- An unconditional action of the full centralizer on the intrinsic form space.
Its dimension and ten-coordinate identification are separate finite certificates. -/
def radicalAction : centralizer →* (Module.End (ZMod 2) radicalForms)ˣ :=
  radicalRepresentation.asGroupHom

set_option maxRecDepth 2048 in
theorem radicalAction_apply (c : centralizer) (R : radicalForms) :
    ((radicalAction c : Module.End (ZMod 2) radicalForms) R : BinaryMatrix) =
      formPullback (centralizerUnit c)⁻¹ (R : BinaryMatrix) := rfl

theorem mem_radicalAction_ker_iff (c : centralizer) :
    c ∈ radicalAction.ker ↔ ∀ R ∈ radicalForms,
      formPullback (centralizerUnit c)⁻¹ R = R := by
  constructor
  · intro hc R hR
    have he := congrArg (fun u : (Module.End (ZMod 2) radicalForms)ˣ =>
      ((u : Module.End (ZMod 2) radicalForms) ⟨R, hR⟩ : BinaryMatrix)) hc
    exact he
  · intro hc
    apply Units.ext
    apply LinearMap.ext
    intro R
    apply Subtype.ext
    exact hc R R.property

end Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
