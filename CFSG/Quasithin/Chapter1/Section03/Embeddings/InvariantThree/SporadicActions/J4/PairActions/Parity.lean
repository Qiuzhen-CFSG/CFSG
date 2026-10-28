module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Overgroups
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Inputs
public import Theory.GroupTheory.SylowOvergroupIncidence
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.SylowNormalizerReduction

/-!
# Odd incidence from conjugacy and Sylow-normalizer control

For two actual max4-type overgroups M and N of the same Sylow subgroup S,
the model conjugacy input supplies an ambient conjugator. Sylow conjugacy
inside M corrects it to an element of the normalizer of S. If this
normalizer equals S, the corrected conjugator fixes M, so M = N.
A nonempty family of overgroups of a pair therefore has cardinality one.

The unconditional `maximalFourPairParity` remains open until the two
model inputs are proved. In particular no count over a proposed list of
conjugates replaces the family in `PairOvergroups`.

Source application: Aschbacher–Smith, printed p.511 (PDF p.528 of
`refs/quasithin.pdf`), citing Aschbacher (1986). That passage does not assert
this incidence count; the theorem below is an explicitly conditional route.
-/

public section

open Subgroup

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction

/-- Reuse the concrete max1 normalizer calculation and M₂₄ Sylow control.
The first hypothesis requires ambient containment, not merely odd index. -/
theorem jankoFourSylowSelfNormalizer_of_max1Normalizer
    (hambient : ∀ [Finite Janko4.Model] [IsSimpleGroup Janko4.Model]
      [Group.IsPerfect Janko4.Model],
      normalizer (Janko4.OuterReduction.OddIndex.twoSubgroup : Set Janko4.Model) ≤
        Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four)
    (hM24 : ∀ S : Sylow 2 Sporadic.Mathieu.M24,
      normalizer (S : Set Sporadic.Mathieu.M24) ≤ S.toSubgroup) :
    JankoFourSylowSelfNormalizer := by
  intro _ _ _ S
  exact Janko4.LocalStructure.SymmetricLinear.sylowNormalizer_le_of_max1Normalizer
    hambient hM24 S

/-- The two model inputs identify any two members of the entire pair family. -/
theorem pairOvergroups_eq_of_sylowNormalizer_of_conjugacy
    (hN : JankoFourSylowSelfNormalizer) (hC : MaximalFourSylowConjugacy)
    [Finite Janko4.Model] [IsSimpleGroup Janko4.Model] [Group.IsPerfect Janko4.Model]
    (S : Sylow 2 Janko4.Model) (R : Subgroup Janko4.Model)
    (M N : PairOvergroups S.toSubgroup R) : M.val = N.val := by
  obtain ⟨g, hg⟩ := hC S M.val N.val M.property.1 N.property.1
    M.property.2.2 N.property.2.2
  have hfix := S.conjugate_overgroup_eq_of_normalizer_le M.val M.property.1
    ((hN S).trans (M.property.1.trans M.val.le_normalizer)) g
    (hg.symm ▸ N.property.1)
  exact hfix.symm.trans hg

/-- Conditional parity assembly; both intrinsic model inputs remain obligations. -/
theorem maximalFourPairParity_of_sylowNormalizer_of_conjugacy
    (hN : JankoFourSylowSelfNormalizer) (hC : MaximalFourSylowConjugacy) :
    MaximalFourPairParity := by
  intro _ _ _ S R _ hne
  exact pairOvergroups_odd_of_unique S.toSubgroup R hne
    (pairOvergroups_eq_of_sylowNormalizer_of_conjugacy hN hC S R)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction
