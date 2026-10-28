module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.SylowCover.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.Reduction

/-!+# Reduction of proper J₄ Sylow-overgroup coverage to maximal embeddings

Reuse the maximal-overgroup isomorphism contract already needed for the J₄
case of 1.3.9. A proper subgroup containing an ambient Sylow lies in a maximal
one. Exhaustion supplies its actual isomorphism with max1, max2 or max4;
the separate embedding comparison then supplies ambient conjugacy. The max2
conjugation certificate places that branch inside a conjugate of C_Model(a).

The two explicit inputs are still unproved. In particular this conditional
assembly is not the unconditional `properSylowOvergroupCover` theorem.

Source: Aschbacher–Smith, printed pp.47–48 and 511 of `refs/quasithin.pdf`,
using Aschbacher, *Overgroups of Sylow subgroups in sporadic groups* (1986);
Kleidman–Wilson, *The maximal subgroups of J₄* (1988), pp.484–510.
-/

public section

open Subgroup Janko4.LocalStructure.SymmetricLinear
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Max4Conjugacy

open SylowCover

/-- Both exhaustive isomorphism classification and actual embedding conjugacy
are required. The finite maximal-overgroup and max2-centralizer steps are
discharged here. -/
theorem properSylowOvergroupCover_of_maximal_models
    (hcover : CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.MaximalSylowCover)
    (hembed : ListedMaximalEmbeddingConjugacy) : ProperSylowOvergroupCover := by
  intro _ _ _ S H hSH hH
  obtain ⟨M, hM, hHM, hSM⟩ := exists_maximal_sylow_overgroup S H hSH hH
  rcases hcover S M hM hSM with htype | htype | htype
  · obtain ⟨g, hg⟩ := hembed S M
      (Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four)
      hM hSM (by simp [listedSubgroups]) htype
    exact ⟨g, Or.inl (hg ▸ hHM)⟩
  · obtain ⟨g, hg⟩ := hembed S M sourceSubgroup hM hSM
      (by simp [listedSubgroups]) htype
    rw [hg] at hHM
    exact ⟨g * h, Or.inr (Or.inl
      (hHM.trans (sourceSubgroup_conjugate_le_centralizer g)))⟩
  · obtain ⟨g, hg⟩ := hembed S M max4Subgroup hM hSM
      (by simp [listedSubgroups]) htype
    exact ⟨g, Or.inr (Or.inr (hg ▸ hHM))⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Max4Conjugacy
