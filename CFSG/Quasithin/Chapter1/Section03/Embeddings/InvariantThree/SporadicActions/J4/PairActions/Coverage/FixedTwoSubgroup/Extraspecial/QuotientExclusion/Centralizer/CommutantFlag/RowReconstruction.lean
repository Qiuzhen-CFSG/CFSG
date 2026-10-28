module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Extraspecial.QuotientExclusion.Centralizer.CommutantFlag.Data

/-!
# Four-seed row reconstruction for the J₄ commutant certificate

A basis of word images of four seed rows reconstructs any matrix commuting
with those words from its four seed rows. This reduces the finite system
from 112² unknown entries to 4·112 entries. The identity is algebraic;
the words, row basis, inverse and ensuing constraints require separate
numerical certificates. See `Data.lean` for the J₄ source context.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.ThirdFlag
open Matrix

/-- Reconstruct a commuting matrix from four seed rows and their word images. -/
theorem row_reconstruction (seeds : Fin 4 → Fin 112) (origin : Fin 112 → Fin 4)
    (W : Fin 112 → Janko4.BinaryMatrix) (Q Qi M : Janko4.BinaryMatrix)
    (hQ : ∀ i, Q i = (W i) (seeds (origin i)))
    (hQi : Qi * Q = 1) (hcomm : ∀ i, Commute M (W i)) :
    M = Qi * (Matrix.of fun i => M (seeds (origin i)) ᵥ* W i) := by
  have hrows : Q * M = (Matrix.of fun i => M (seeds (origin i)) ᵥ* W i) := by
    funext i
    rw [mul_apply_eq_vecMul, hQ, ← mul_apply_eq_vecMul,
      ← (hcomm i).eq, mul_apply_eq_vecMul]
    rfl
  calc
    M = Qi * (Q * M) := by rw [← mul_assoc, hQi, one_mul]
    _ = _ := congrArg (Qi * ·) hrows

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.ThirdFlag
