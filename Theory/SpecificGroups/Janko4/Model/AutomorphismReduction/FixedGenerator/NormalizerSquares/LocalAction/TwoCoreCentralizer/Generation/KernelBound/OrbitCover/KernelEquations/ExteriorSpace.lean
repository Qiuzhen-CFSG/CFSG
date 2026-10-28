module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.ExteriorData

/-!
# The explicit candidate space of alternating forms

This module only decodes the finite numerical data and takes their linear
span. It asserts no group invariance, dimension, or kernel restriction.
The proposed route and source references are in source/README.md.
-/

@[expose] public section
open scoped Matrix

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates

/-- Index of (i,j), i < j, in the lexicographic upper triangle. -/
def exteriorIndex (i j : Fin 112) : ℕ :=
  i.val * (223 - i.val) / 2 + (j.val - i.val - 1)

/-- Decode an alternating form, with a zero diagonal. -/
def decodeExteriorForm (r : ℕ) : BinaryMatrix := fun i j =>
  if i < j then (if r.testBit (exteriorIndex i j) then 1 else 0)
  else if j < i then (if r.testBit (exteriorIndex j i) then 1 else 0)
  else 0

def exteriorBasisForm (i : Fin 1221) : BinaryMatrix :=
  decodeExteriorForm (exteriorFormRows.get i)

/-- The span of explicit forms; this definition mentions neither group membership
nor the required column equations. -/
def exteriorFormSpace : Submodule (ZMod 2) BinaryMatrix :=
  Submodule.span (ZMod 2) (Set.range exteriorBasisForm)

theorem exteriorBasisForm_mem (i : Fin 1221) : exteriorBasisForm i ∈ exteriorFormSpace :=
  Submodule.subset_span ⟨i, rfl⟩

theorem decodeExteriorForm_diagonal (r : ℕ) (i : Fin 112) :
    decodeExteriorForm r i i = 0 := by simp [decodeExteriorForm]

theorem decodeExteriorForm_transpose (r : ℕ) :
    (decodeExteriorForm r)ᵀ = decodeExteriorForm r := by
  ext i j
  simp only [Matrix.transpose_apply, decodeExteriorForm]
  by_cases h : i < j
  · simp [h, not_lt_of_gt h]
  · by_cases h' : j < i <;> simp [h, h']

attribute [local irreducible] exteriorFormSpace formPullback

private theorem formPullback_injective (g : BinaryMatrixˣ) :
    Function.Injective (formPullback g) := by
  intro R S h
  have he := congrArg (formPullback g⁻¹) h
  simpa only [← formPullback_mul, mul_inv_cancel, formPullback_one] using he

private theorem mem_formStabilizer_of_maps (g : BinaryMatrixˣ)
    (h : ∀ R ∈ exteriorFormSpace, formPullback g R ∈ exteriorFormSpace) :
    g ∈ formStabilizer exteriorFormSpace := by
  let f : exteriorFormSpace → exteriorFormSpace := fun R => ⟨formPullback g R, h R R.property⟩
  have hf : Function.Injective f := by
    intro R S he
    exact Subtype.ext (formPullback_injective g
      (congrArg (fun x : exteriorFormSpace => (x : BinaryMatrix)) he))
  intro R
  constructor
  · intro hR
    obtain ⟨S, hS⟩ := Finite.surjective_of_injective hf ⟨formPullback g R, hR⟩
    have he : (S : BinaryMatrix) = R :=
      formPullback_injective g
        (congrArg (fun x : exteriorFormSpace => (x : BinaryMatrix)) hS)
    exact he ▸ S.property
  · exact h R

/-- In finite dimension over this finite field, one-sided preservation of the
explicit spanning family suffices for setwise preservation of the whole space. -/
theorem mem_formStabilizer_of_basis (g : BinaryMatrixˣ)
    (h : ∀ i : Fin 1221, formPullback g (exteriorBasisForm i) ∈ exteriorFormSpace) :
    g ∈ formStabilizer exteriorFormSpace := by
  apply mem_formStabilizer_of_maps g
  intro R hR
  simp only [exteriorFormSpace] at hR
  induction hR using Submodule.span_induction with
  | mem R hR =>
    obtain ⟨i, rfl⟩ := hR
    exact h i
  | zero => simp [formPullback]
  | add R S _ _ hR hS =>
    simpa only [formPullback, Matrix.mul_add, Matrix.add_mul] using
      exteriorFormSpace.add_mem hR hS
  | smul r R _ hR =>
    simpa only [formPullback, Matrix.mul_smul, Matrix.smul_mul] using
      exteriorFormSpace.smul_mem r hR


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates
