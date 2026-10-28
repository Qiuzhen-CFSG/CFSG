module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.Coordinates

/-!
# Ambient form stabilizers and the literal homology condition

Pullback of a bilinear form by matrix units is a right action. Its setwise
and pointwise stabilizers are subgroups, so checking the two published
generators suffices for the entire matrix group. The homology-kernel
condition is also expressed in raw columns, retaining the exact quotient
ker(a - 1) / im(a - 1). No local-subgroup generation is used.

Source conventions: Model.Data and OrbitCover/source/README.md.
-/

@[expose] public section
open scoped Matrix

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates

def formPullback (g : BinaryMatrixˣ) (R : BinaryMatrix) : BinaryMatrix :=
  (g : BinaryMatrix)ᵀ * R * (g : BinaryMatrix)

theorem formPullback_one (R : BinaryMatrix) : formPullback 1 R = R := by
  simp [formPullback]

theorem formPullback_mul (g h : BinaryMatrixˣ) (R : BinaryMatrix) :
    formPullback (g * h) R = formPullback h (formPullback g R) := by
  simp only [formPullback, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]

def formStabilizer (W : Submodule (ZMod 2) BinaryMatrix) : Subgroup BinaryMatrixˣ where
  carrier := {g | ∀ R, formPullback g R ∈ W ↔ R ∈ W}
  one_mem' := by intro R; rw [formPullback_one]
  mul_mem' := by
    intro g h hg hh R
    rw [formPullback_mul]
    exact (hh _).trans (hg R)
  inv_mem' := by
    intro g hg R
    have he := hg (formPullback g⁻¹ R)
    rw [← formPullback_mul, inv_mul_cancel, formPullback_one] at he
    exact he.symm

theorem matrixGroup_le_formStabilizer (W : Submodule (ZMod 2) BinaryMatrix)
    (ha : matrixUnitA ∈ formStabilizer W)
    (hb : matrixUnitB ∈ formStabilizer W) : matrixGroup ≤ formStabilizer W := by
  apply (matrixGroup_le_iff _).mpr
  intro g hg
  rcases hg with hg | hg
  · have h : g = matrixUnitA := Units.ext hg
    exact h ▸ ha
  · have h : g = matrixUnitB := Units.ext hg
    exact h ▸ hb

/-- The subgroup fixing a single bilinear form, without a nondegeneracy premise. -/
def formFixer (R : BinaryMatrix) : Subgroup BinaryMatrixˣ where
  carrier := {g | formPullback g R = R}
  one_mem' := formPullback_one R
  mul_mem' := by
    intro g h hg hh
    change formPullback (g * h) R = R
    rw [formPullback_mul, hg, hh]
  inv_mem' := by
    intro g hg
    have he := congrArg (formPullback g⁻¹) hg
    rw [← formPullback_mul, mul_inv_cancel, formPullback_one] at he
    exact he.symm

theorem matrixGroup_le_formFixer (R : BinaryMatrix)
    (ha : formPullback matrixUnitA R = R)
    (hb : formPullback matrixUnitB R = R) : matrixGroup ≤ formFixer R := by
  apply (matrixGroup_le_iff _).mpr
  intro g hg
  rcases hg with hg | hg
  · have h : g = matrixUnitA := Units.ext hg
    exact h ▸ ha
  · have h : g = matrixUnitB := Units.ext hg
    exact h ▸ hb

def KernelConditions (g : BinaryMatrixˣ) : Prop :=
  (g : BinaryMatrix) * matrixA = matrixA * (g : BinaryMatrix) ∧
    ∀ v : NaturalModule, matrixA *ᵥ v = v →
      ∃ w : NaturalModule, (g : BinaryMatrix) *ᵥ v - v = matrixA *ᵥ w - w

theorem kernel_conditions (c : homologyAction.ker) :
    KernelConditions ((c : involutionCentralizer) : BinaryMatrixˣ) := by
  constructor
  · have hc := ((mem_involutionCentralizer_iff _).mp
      (c : involutionCentralizer).property).2
    simpa only [Units.val_mul, coe_matrixUnitA] using
      congrArg (fun u : BinaryMatrixˣ => (u : BinaryMatrix)) hc
  · intro v hv
    have hv' : v ∈ fixedVectors := by
      change displacement v = 0
      rw [displacement_apply, hv, sub_self]
    have hc := (mem_homologyAction_ker_iff _).mp c.property ⟨v, hv'⟩
    obtain ⟨w, hw⟩ := hc
    exact ⟨w, (by simpa only [displacement_apply, naturalAction_apply] using hw.symm)⟩


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates
