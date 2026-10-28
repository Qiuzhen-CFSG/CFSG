module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.OctonionLocals

/-!
# The exact octonion graph extension

Peirce blocks act faithfully, fix both diagonal idempotents, and are normalized
by the prescribed graph word. The graph word exchanges those idempotents, so it
lies outside the block image. Its matrix automorphism is inverse transpose
conjugated by the permutation exchanging Peirce coordinates 1 and 2.

These identities feed the literal subgroup extension in `Long.Subgroup`.
Source: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, p.283. The octonion
conventions are those of the existing attributed ATLAS ports.
-/

@[expose] public section
open Matrix Atlas.SplitOctonion
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long
open OctonionLocals PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight.BlockRealization

variable {K : Type*} [Field K] [CharP K 2]

/-- The permutation of the last two Peirce coordinates. -/
noncomputable def graphFlip : SL(3,K) :=
  ⟨!![1,0,0;0,0,1;0,1,0], by simp [Matrix.det_fin_three, CharTwo.neg_eq]⟩
/-- Inverse transpose in the precise octonion graph convention. -/
noncomputable def graphTwist (A : SL(3,K)) : SL(3,K) := graphFlip * A⁻¹.transpose * graphFlip

omit [CharP K 2] in
/-- Peirce restriction recovers the original determinant-one matrix. -/
theorem block_injective : Function.Injective (blockHom (K := K)) := by
  intro A B h
  apply Subtype.ext
  simpa only [peirceMatrix_blockHom] using congrArg
    PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight.peirceMatrix h

/-- The prescribed Weyl word is an involution. -/
theorem graph_square : (graph : Model K) * graph = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change graph.val (graph.val x) = x
  rw [graph_apply, graph_apply]
  ext i
  fin_cases i <;> rfl

/-- The graph word acts by inverse transpose with the Peirce permutation. -/
theorem graph_block (A : SL(3,K)) :
    (graph : Model K) * blockHom A = blockHom (graphTwist A) * graph := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change graph.val ((blockHom A).val x) = (blockHom (graphTwist A)).val (graph.val x)
  rw [graph_apply, graph_apply]
  have ht : (graphTwist A).val = (graphFlip (K := K)).val * cofactor A.val * graphFlip.val := rfl
  have cm (B C : Matrix (Fin 3) (Fin 3) K) : cofactor (B * C) = cofactor B * cofactor C := by
    simp only [cofactor, Matrix.adjugate_mul_distrib, Matrix.transpose_mul]
  have cf : cofactor (graphFlip (K := K)).val = graphFlip.val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [graphFlip, cofactor, Matrix.adjugate_fin_three, CharTwo.neg_eq]
  have ct : cofactor (graphTwist A).val = graphFlip.val * A.val * graphFlip.val := by
    rw [ht, cm, cm, cf, cofactor_cofactor]
  change ![(cofactor A.val *ᵥ ![x 7,x 2,x 1]) 0,
      (A.val *ᵥ ![x 0,x 5,x 6]) 1, (A.val *ᵥ ![x 0,x 5,x 6]) 2,
      x 4, x 3, (cofactor A.val *ᵥ ![x 7,x 2,x 1]) 2,
      (cofactor A.val *ᵥ ![x 7,x 2,x 1]) 1, (A.val *ᵥ ![x 0,x 5,x 6]) 0] =
    pack (x 4) (x 3) ((graphTwist A).val *ᵥ ![x 7,x 1,x 2])
      (cofactor (graphTwist A).val *ᵥ ![x 0,x 6,x 5])
  rw [ct, ht]
  ext i
  fin_cases i <;> simp [graphFlip, pack, Matrix.mul_apply,
    Matrix.mulVec, Matrix.vecMul, dotProduct, Fin.sum_univ_three] <;> ring

/-- Blocks fix the two diagonal idempotents; the graph word exchanges them. -/
theorem graph_not_block : (graph : Model K) ∉ (blockHom (K := K)).range := by
  rintro ⟨A, hA⟩
  have h := congrArg (fun g : Model K => g.val (basisVector 3) 4) hA
  rw [blockHom_fixes_three, graph_apply] at h
  simp [basisVector] at h

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long
