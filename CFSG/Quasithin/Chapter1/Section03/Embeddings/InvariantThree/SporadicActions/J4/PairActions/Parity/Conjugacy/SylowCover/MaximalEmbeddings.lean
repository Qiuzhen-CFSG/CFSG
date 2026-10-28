module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.SylowCover.MaximalEmbeddings.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.SylowCover.MaximalEmbeddings.Max2

/-!
# Assembly of the three literal J₄ maximal-embedding comparisons

The max2 comparison is proved using the unique nonidentity central element
of its Sylow subgroups. The max1 and max4 comparisons remain separate inputs;
this conditional assembly does not assert `listedMaximalEmbeddingConjugacy`.
Each input concerns actual ambient conjugacy of the specified word subgroup,
independently of exhaustive classification by abstract isomorphism type.

Source context: Kleidman–Wilson, *The maximal subgroups of J₄*, Proc. London
Math. Soc. 56 (1988), 484–510. The application on printed p.511 of
`refs/quasithin.pdf` cites Aschbacher's Sylow-overgroup analysis (1986).
-/

public section

open Janko4.LocalStructure.SymmetricLinear

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Max4Conjugacy.SylowCover

/-- The remaining two embedding comparisons complete the list; the max2
branch is discharged by its proved Sylow-center argument. -/
theorem listedMaximalEmbeddingConjugacy_of_max1_max4
    (hmax1 : MaximalEmbeddingConjugacyAt
      (Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four))
    (hmax4 : MaximalEmbeddingConjugacyAt max4Subgroup) :
    ListedMaximalEmbeddingConjugacy := by
  intro _ _ _ S M L hM hSM hL he
  simp only [listedSubgroups, Set.mem_insert_iff, Set.mem_singleton_iff] at hL
  rcases hL with rfl | rfl | rfl
  · exact hmax1 S M hM hSM he
  · exact max2MaximalEmbeddingConjugacy S M hM hSM he
  · exact hmax4 S M hM hSM he

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Max4Conjugacy.SylowCover
