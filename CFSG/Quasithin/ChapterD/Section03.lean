module

public import CFSG.Quasithin.ChapterD.Section03.Basic

/-!
# Modules with q̂ ≤ 2

This is the arithmetic interface for Aschbacher--Smith §D.3 (printed
pp. 192–208).  The structural alternatives in Theorems D.3.10 and D.3.21
are assembled from the simple-module list in §B.4 and the predecessor results
of §D.2.  Their common numerical input is re-exported here under the source
section namespace, so later local analyses can use it without depending on a
particular representation implementation.
-/

namespace CFSG.Quasithin.ChapterD.Section03

/-- Source equation (∗) in Lemmas D.3.5–D.3.10: a decomposition into blocks
whose individual cubic parameters satisfy the bound has total parameter at
most two. -/
public theorem lemma_D_3_rank_sum
    {ι : Type*} [Fintype ι] (p : ι → QHatProfile) :
    (∑ i, (p i).codim) ≤ 2 * ∑ i, (p i).offenderRank :=
  sum_codim_le_two_mul_sum_offenderRank p

/-- The strict branch used in D.3.13 and D.3.19: one strict chief-factor
estimate forces strictness for the assembled module. -/
public theorem lemma_D_3_strict_rank_sum
    {ι : Type*} [Fintype ι] (p : ι → QHatProfile)
    (j : ι) (hj : (p j).codim < 2 * (p j).offenderRank)
    (hrest : ∀ i, i ≠ j → (p i).codim ≤ 2 * (p i).offenderRank) :
    (∑ i, (p i).codim) < 2 * ∑ i, (p i).offenderRank :=
  sum_codim_lt_two_mul_sum_offenderRank p j hj hrest

end CFSG.Quasithin.ChapterD.Section03
