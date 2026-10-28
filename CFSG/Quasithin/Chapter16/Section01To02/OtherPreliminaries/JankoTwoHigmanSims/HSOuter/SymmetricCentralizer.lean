module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.Representatives
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.Statements
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.SymmetricCentralizer.Embedding
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.SymmetricCentralizer.Cardinality

/-!
# The symmetric outer HS centralizer is S₈

Seven explicit HS words satisfying the type-A₇ Coxeter relations give a faithful
homomorphism from the actual symmetric group S₈ to the centralizer of the exact
`symmetricPermutation`. A graph-refinement certificate bounds the graph
centralizer by 80,640. Parity halves that bound inside HS, so the embedding
is onto. The resulting multiplicative equivalence concerns the fixed ATLAS
carrier, not an unconnected model or an order-based group-family label.

This is the representative centralizer calculation for Aschbacher–Smith
16.1.5(10), printed p.1172, and GLS3 Table 5.3m, class 2D. Exhaustive fusion
and normalizer membership of the representative belong to the outer-centralizer
assembly and are not premises of this calculation.
-/

public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSOuter

private theorem symmetricEmbedding_surjective :
    Function.Surjective SymmetricCentralizer.embedding := by
  apply (SymmetricCentralizer.embedding_injective.bijective_of_nat_card_le ?_).2
  calc
    Nat.card (permutationCentralizer symmetricPermutation) ≤ 40320 :=
      SymmetricCentralizer.centralizer_card_le
    _ = Nat.card S8 := by rw [Nat.card_perm, Nat.card_fin]; rfl

/-- An actual multiplicative equivalence from the specified centralizer to S₈. -/
noncomputable def symmetricCentralizerEquiv :
    permutationCentralizer symmetricPermutation ≃* S8 :=
  (MulEquiv.ofBijective SymmetricCentralizer.embedding
    ⟨SymmetricCentralizer.embedding_injective, symmetricEmbedding_surjective⟩).symm

/-- The symmetric outer representative has centralizer isomorphic to S₈. -/
theorem symmetricCentralizer_nonempty_mulEquiv :
    Nonempty (permutationCentralizer symmetricPermutation ≃* S8) :=
  ⟨symmetricCentralizerEquiv⟩

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSOuter
