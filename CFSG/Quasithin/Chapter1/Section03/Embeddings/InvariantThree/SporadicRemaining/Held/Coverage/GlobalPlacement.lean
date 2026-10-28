module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Held.Reductions
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Covers
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Reduction
public import Theory.SpecificGroups.Held.Model.Basic
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.Placement

/-!
# Exhaustive placement of Held Sylow pairs

The source pair has a genuine Sylow two-subgroup, and permutability makes
its join with the odd complement a group with only two and three as prime
divisors. These existing hypotheses discharge all the abstract group inputs
to the certified `placement` theorem. Thus `pair_local_placement` places every
source pair inside a conjugate of one of the literal ATLAS max3/max4 subgroups.
The original conditional finite-check adapter is preserved below.

This proves the direct pair-placement contract. The uniform plane and full
extending-action calculations remain with the Held branch assembly; this
module does not assert the source's unrestricted sporadic exclusion.

Sources: Aschbacher–Smith, printed pp.509–511; GLS3, Table 5.3p; the ATLAS
max3/max4 programs used by `PairCoverage.LocalSubgroups`.
-/

public section

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.HeldPairs

open Subgroup Held.LocalPairs.PairCoverage.SylowOvergroups

/-- All source inputs for the direct route follow from `PairInput`.
Final assembly must prove the four explicit concrete premises. -/
theorem pair_local_placement_of_finite_checks
    (hP : IsPGroup 2 markedSubgroup)
    (halign : ∀ i, markedSubgroup ≤ alignedOvergroup i)
    (hcover : Covers) (hcheck : RepresentativeChecks)
    {S : Sylow 2 Held.He} {R : Subgroup Held.He} (h : PairInput S R) :
    ∃ (i : Bool) (g : Held.He),
      (R ⊔ (S : Subgroup Held.He)).map (MulAut.conj g).toMonoidHom ≤
        Held.LocalPairs.PairCoverage.localOvergroup i := by
  apply placement_of_tests hP halign hcover hcheck
  · exact fun hd => S.not_dvd_index
      (hd.trans (index_dvd_of_le (show (S : Subgroup Held.He) ≤ R ⊔ S from le_sup_right)))
  · exact fun _ hp hd => EvenRankTwo.product_prime_divisors h hp hd

/-- Every source Sylow pair is conjugate into one of the two literal ATLAS
local subgroups. All finite calculation premises have been discharged. -/
theorem pair_local_placement
    {S : Sylow 2 Held.He} {R : Subgroup Held.He} (h : PairInput S R) :
    ∃ (i : Bool) (g : Held.He),
      (R ⊔ (S : Subgroup Held.He)).map (MulAut.conj g).toMonoidHom ≤
        Held.LocalPairs.PairCoverage.localOvergroup i := by
  apply placement
  · exact fun hd => S.not_dvd_index
      (hd.trans (index_dvd_of_le (show (S : Subgroup Held.He) ≤ R ⊔ S from le_sup_right)))
  · exact fun _ hp hd => EvenRankTwo.product_prime_divisors h hp hd

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.HeldPairs
