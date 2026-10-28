module

public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.FourSpaceAction.SectionMatrices
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.Permutations
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Algebra.Field.ZMod

/-!
# Nine genuine four-spaces in the Thompson max3 factor

Right inverses prove dimension four, separating linear functionals prove
that the nine row spans are distinct, and the two explicit change-of-basis
families prove the factor-matrix transitions. Every numerical identity is
checked by Lean's kernel using the published packed binary matrix checker.

The underlying bases and factors are the frozen witnesses in
`AlternatingQuotient/source/action_witness.json`; see that directory for
ATLAS attribution. This is the subspace geometry for GLS3 Table 5.3x and
Aschbacher--Smith A.2.19, not a nine-vector orbit.
-/

public section
open scoped Matrix
namespace Thompson.InvolutionCentralizer.AlternatingQuotient

@[expose] def blockRightInverseRows : Fin 9 → Array ℕ :=
  ![#[1, 4, 9, 0, 0, 14, 0, 0],
    #[15, 6, 1, 3, 0, 0, 0, 0],
    #[3, 12, 7, 0, 0, 0, 2, 0],
    #[3, 0, 12, 1, 0, 0, 0, 9],
    #[12, 1, 0, 5, 7, 0, 0, 0],
    #[8, 2, 13, 0, 0, 1, 0, 0],
    #[7, 14, 0, 0, 4, 0, 5, 0],
    #[9, 7, 11, 8, 0, 0, 0, 0],
    #[3, 2, 11, 0, 6, 0, 0, 0]]

@[expose] def blockRightInverse (i : Fin 9) : Matrix (Fin 8) (Fin 4) (ZMod 2) :=
  decodeRows 8 4 (blockRightInverseRows i)

@[expose] def blockTransitionARows : Fin 9 → Array ℕ :=
  ![#[1, 2, 4, 8],
    #[1, 2, 4, 8],
    #[1, 2, 15, 8],
    #[1, 2, 15, 8],
    #[2, 4, 1, 8],
    #[4, 1, 2, 8],
    #[1, 4, 3, 8],
    #[1, 5, 2, 8],
    #[4, 2, 1, 13]]

@[expose] def blockTransitionA (i : Fin 9) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  decodeRows 4 4 (blockTransitionARows i)

@[expose] def blockTransitionBRows : Fin 9 → Array ℕ :=
  ![#[2, 4, 8, 11],
    #[1, 2, 4, 8],
    #[1, 2, 8, 4],
    #[1, 3, 8, 12],
    #[1, 2, 4, 8],
    #[4, 8, 7, 10],
    #[2, 5, 1, 12],
    #[1, 2, 8, 13],
    #[8, 1, 12, 10]]

@[expose] def blockTransitionB (i : Fin 9) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  decodeRows 4 4 (blockTransitionBRows i)

@[expose] def blockSeparatorRows : Fin 9 → Fin 9 → ℕ :=
  ![![0,
    67,
    23,
    3,
    7,
    11,
    9,
    41,
    13],
    ![18,
    0,
    36,
    76,
    7,
    16,
    6,
    143,
    13],
    ![18,
    30,
    0,
    3,
    7,
    11,
    9,
    20,
    13],
    ![8,
    30,
    10,
    0,
    43,
    11,
    9,
    41,
    13],
    ![18,
    128,
    10,
    3,
    0,
    11,
    49,
    20,
    13],
    ![70,
    42,
    36,
    32,
    43,
    0,
    49,
    41,
    37],
    ![18,
    30,
    23,
    21,
    43,
    16,
    0,
    20,
    37],
    ![8,
    30,
    10,
    3,
    7,
    101,
    49,
    0,
    37],
    ![8,
    42,
    36,
    21,
    74,
    11,
    6,
    41,
    0]]

@[expose] def blockSeparator (i j : Fin 9) : Fin 8 → ZMod 2 :=
  fun k => BinaryMatrix.bit (blockSeparatorRows i j) k.val

theorem blockBasis_mul_rightInverse (i : Fin 9) :
    blockBasis i * blockRightInverse i = 1 := by
  apply decodeRows_mul_one
  revert i
  decide +kernel

theorem blockBasis_mul_factorA (i : Fin 9) :
    blockBasis i * factorAMatrix = blockTransitionA i * blockBasis (permA⁻¹ i) := by
  apply decodeRows_mul_eq
  revert i
  decide +kernel

theorem blockBasis_mul_factorB (i : Fin 9) :
    blockBasis i * factorBMatrix = blockTransitionB i * blockBasis (permB⁻¹ i) := by
  apply decodeRows_mul_eq
  revert i
  decide +kernel

private theorem blockSeparator_check : ∀ i j : Fin 9, i ≠ j →
    blockBasis j *ᵥ blockSeparator i j = 0 ∧
    blockBasis i 0 ⬝ᵥ blockSeparator i j = 1 := by
  have h : (List.finRange 9).all (fun i => (List.finRange 9).all (fun j =>
      if i = j then true else
        (List.finRange 4).all (fun k => decide
          ((blockBasis j *ᵥ blockSeparator i j) k = 0)) &&
        decide (blockBasis i 0 ⬝ᵥ blockSeparator i j = 1))) = true := by
    decide +kernel
  simp only [List.all_eq_true, List.mem_finRange, forall_const] at h
  intro i j hij
  specialize h i j
  simp only [hij, ↓reduceIte, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const, decide_eq_true_eq] at h
  exact ⟨funext h.1, h.2⟩

theorem blockSpace_eq_range (i : Fin 9) :
    blockSpace i = LinearMap.range (blockBasis i).vecMulLinear := by
  exact (range_vecMulLinear _).symm

theorem blockSpace_injective : Function.Injective blockSpace := by
  intro i j h
  by_contra hij
  have hm : blockBasis i 0 ∈ blockSpace j := by
    rw [← h]
    exact Submodule.subset_span ⟨0, rfl⟩
  rw [blockSpace_eq_range] at hm
  obtain ⟨c, hc⟩ := hm
  have hs := blockSeparator_check i j hij
  have he : (0 : ZMod 2) = 1 := by
    calc
      0 = c ⬝ᵥ (blockBasis j *ᵥ blockSeparator i j) := by rw [hs.1, dotProduct_zero]
      _ = (c ᵥ* blockBasis j) ⬝ᵥ blockSeparator i j := Matrix.dotProduct_mulVec _ _ _
      _ = blockBasis i 0 ⬝ᵥ blockSeparator i j := by rw [show c ᵥ* blockBasis j = blockBasis i 0 from hc]
      _ = 1 := hs.2
  exact zero_ne_one he

theorem blockBasis_vecMul_injective (i : Fin 9) :
    Function.Injective (blockBasis i).vecMulLinear := by
  intro x y h
  have := congrArg (fun v => v ᵥ* blockRightInverse i) h
  simpa only [Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul,
    blockBasis_mul_rightInverse, Matrix.vecMul_one] using this

theorem blockSpace_finrank (i : Fin 9) :
    Module.finrank (ZMod 2) (blockSpace i) = 4 := by
  rw [blockSpace_eq_range, LinearMap.finrank_range_of_inj (blockBasis_vecMul_injective i)]
  simp

theorem blockSpace_factorA (i : Fin 9) {v : Fin 8 → ZMod 2} (hv : v ∈ blockSpace i) :
    v ᵥ* factorAMatrix ∈ blockSpace (permA⁻¹ i) := by
  rw [blockSpace_eq_range] at hv ⊢
  obtain ⟨c, rfl⟩ := hv
  refine ⟨c ᵥ* blockTransitionA i, ?_⟩
  change (c ᵥ* blockTransitionA i) ᵥ* blockBasis (permA⁻¹ i) = (c ᵥ* blockBasis i) ᵥ* factorAMatrix
  rw [Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, blockBasis_mul_factorA]

theorem blockSpace_factorB (i : Fin 9) {v : Fin 8 → ZMod 2} (hv : v ∈ blockSpace i) :
    v ᵥ* factorBMatrix ∈ blockSpace (permB⁻¹ i) := by
  rw [blockSpace_eq_range] at hv ⊢
  obtain ⟨c, rfl⟩ := hv
  refine ⟨c ᵥ* blockTransitionB i, ?_⟩
  change (c ᵥ* blockTransitionB i) ᵥ* blockBasis (permB⁻¹ i) = (c ᵥ* blockBasis i) ᵥ* factorBMatrix
  rw [Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, blockBasis_mul_factorB]

private def factorBInverseRows : Array ℕ := #[150, 53, 172, 38, 174, 100, 232, 196]

private theorem factorA_mul_self : factorAMatrix * factorAMatrix = 1 := by
  apply decodeRows_mul_one
  decide +kernel

private theorem factorB_mul_inverse :
    factorBMatrix * decodeRows 8 8 factorBInverseRows = 1 := by
  apply decodeRows_mul_one
  decide +kernel

private theorem blockSpace_map_of_factor
    (F F' : Matrix (Fin 8) (Fin 8) (ZMod 2)) (hF : F * F' = 1)
    (i j : Fin 9) (h : ∀ v ∈ blockSpace i, v ᵥ* F ∈ blockSpace j) :
    (blockSpace i).map F.vecMulLinear = blockSpace j := by
  have hinj : Function.Injective F.vecMulLinear := by
    intro x y hxy
    have ht := congrArg (fun v => v ᵥ* F') hxy
    simpa only [Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul,
      hF, Matrix.vecMul_one] using ht
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨v, hv, rfl⟩
    exact h v hv
  · rw [← (Submodule.equivMapOfInjective _ hinj _).finrank_eq,
      blockSpace_finrank, blockSpace_finrank]

/-- The first factor matrix permutes the literal row spans, with the right-action convention. -/
theorem blockSpace_map_factorA (i : Fin 9) :
    (blockSpace i).map factorAMatrix.vecMulLinear = blockSpace (permA⁻¹ i) :=
  blockSpace_map_of_factor _ _ factorA_mul_self _ _ (fun _ => blockSpace_factorA i)

/-- The second factor matrix permutes the literal row spans, with the right-action convention. -/
theorem blockSpace_map_factorB (i : Fin 9) :
    (blockSpace i).map factorBMatrix.vecMulLinear = blockSpace (permB⁻¹ i) :=
  blockSpace_map_of_factor _ _ factorB_mul_inverse _ _ (fun _ => blockSpace_factorB i)

end Thompson.InvolutionCentralizer.AlternatingQuotient
