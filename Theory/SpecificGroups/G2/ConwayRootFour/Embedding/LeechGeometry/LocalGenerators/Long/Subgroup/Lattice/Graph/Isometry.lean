module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Graph.Certificates

/-!
# The concrete integral graph swap

The checked matrix preserves the displayed lattice and its form. Transport
through the published comparison constructs an actual Leech isometry whose
square is negation; it need not be involutory in Co₀.
Source: Aschbacher, Sporadic Groups (1994), 49.5, p.283. The numerical
certificates and their ATLAS provenance are recorded in `Graph.Data`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Atlas.Algebra Atlas.Lattices Atlas.Conway Atlas.LinearAlgebra
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Graph
open Block Block.Realization

def swapUnit : GL Index ℚ :=
  ⟨swapMatrix, -swapMatrix, by rw [mul_neg, swapMatrix_square, neg_neg],
    by rw [neg_mul, swapMatrix_square, neg_neg]⟩

def swapLinear : Space ≃ₗ[ℚ] Space := linearMatrices swapUnit

theorem swapLinear_apply (x : Space) : swapLinear x = swapMatrix *ᵥ x := rfl

theorem swapLinear_square : swapLinear * swapLinear = LinearEquiv.neg ℚ := by
  ext x i
  change (swapMatrix *ᵥ (swapMatrix *ᵥ x)) i = -x i
  rw [Matrix.mulVec_mulVec, swapMatrix_square, Matrix.neg_mulVec, Matrix.one_mulVec]
  rfl

theorem swapLinear_form (x y : Space) : form (swapLinear x) (swapLinear y) = form x y :=
  preserves_form_of_gram swapMatrix swapMatrix_gram x y

theorem swapLinear_lattice (x : Space) : x ∈ lattice ↔ swapLinear x ∈ lattice := by
  have hf := preserves_lattice_of_coordinates swapMatrix coordinates swapMatrix_basis
  refine ⟨hf x, fun hx => ?_⟩
  have hh := lattice.neg_mem (hf _ hx)
  simpa only [swapLinear_apply, Matrix.mulVec_mulVec, swapMatrix_square,
    Matrix.neg_mulVec, Matrix.one_mulVec, neg_neg] using hh

def comparedSwap : RationalCoordinates ≃ₗ[ℚ] RationalCoordinates :=
  linearAutomorphismCongr matrixComparison swapLinear

theorem comparedSwap_isometry : comparedSwap ∈ rationalLatticeIsometries := by
  constructor
  · intro x y
    change rationalForm (matrixComparison (swapLinear (matrixComparison.symm x)))
      (matrixComparison (swapLinear (matrixComparison.symm y))) = _
    rw [matrixComparison_form, swapLinear_form]
    simpa only [LinearEquiv.apply_symm_apply] using
      (matrixComparison_form (matrixComparison.symm x) (matrixComparison.symm y)).symm
  · intro x
    change x ∈ rationalLeech ↔ matrixComparison (swapLinear (matrixComparison.symm x)) ∈ rationalLeech
    rw [← matrixComparison_lattice, ← swapLinear_lattice]
    simpa only [LinearEquiv.apply_symm_apply] using (matrixComparison_lattice (matrixComparison.symm x)).symm

/-- The explicit integral graph candidate on the retained Leech lattice. -/
def swap : LeechIsometryGroup := fullIsometryEquiv.symm ⟨comparedSwap, comparedSwap_isometry⟩

theorem swap_extension : (fullIsometryEquiv swap).val = comparedSwap :=
  congrArg Subtype.val (fullIsometryEquiv.apply_symm_apply _)

theorem swap_intertwines (x : Space) :
    (fullIsometryEquiv swap).val (matrixComparison x) = matrixComparison (swapLinear x) := by
  rw [swap_extension]
  change matrixComparison (swapLinear (matrixComparison.symm (matrixComparison x))) = _
  rw [matrixComparison.symm_apply_apply]

/-- This normalizer has order four in Co₀ and involutory image in its sign quotient. -/
theorem swap_square : swap * swap = negationIsometry := by
  have hn : (fullIsometryEquiv negationIsometry).val = LinearEquiv.neg ℚ := by
    apply LinearEquiv.toLinearMap_injective
    symm
    exact rationalExtension_unique negationIsometry.val
      (-LinearMap.id : RationalCoordinates →ₗ[ℚ] RationalCoordinates) (by
        intro x
        rw [negationIsometry_apply]
        simp)
  apply fullIsometryEquiv.injective
  rw [map_mul]
  apply Subtype.ext
  change (fullIsometryEquiv swap).val * (fullIsometryEquiv swap).val = _
  rw [swap_extension, hn]
  change linearAutomorphismCongr matrixComparison swapLinear *
    linearAutomorphismCongr matrixComparison swapLinear = _
  rw [← map_mul, swapLinear_square]
  ext x
  simp

theorem swap_square_mem : swap * swap ∈ leechCentralSigns := by
  rw [swap_square, leechCentralSigns_mem]
  exact Or.inr rfl

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Graph
