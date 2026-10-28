module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Descent
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Coverage.Lower
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Coverage.Upper

/-!
# Exhaustive coverage of the second Held kernel candidates

Every centric subgroup of the fixed Sylow group which is not contained in the
transfer kernel is conjugate inside that Sylow group to one of the 45 published
representatives. The checked binary Schreier certificates cover every maximal
subgroup of every representative. Maximal-chain descent then covers every
eligible subgroup, since eligibility is upward closed and conjugacy invariant.
Intrinsic radicality is never used to prune the census.

The 225 checked branches comprise 45 subgroups inside the kernel, 66 with
outside centralizer witnesses, and 114 with word-certified conjugacies.
All equations are checked on the existing actual permutation carrier.
Source problem: Huppert--Blackburn III, XII.1.18(b), printed p.314. This is the
finite coverage step of the proposed transfer argument, not its final assembly.
-/

namespace Theory.GroupTheory.HeldM22A10.SecondExclusion.ForceNormalizer.Candidates

/-- Every actual centric subgroup outside the transfer kernel is represented,
without an intrinsic-radicality hypothesis or further certificate premises. -/
public theorem coverage : Coverage := by
  apply coverage_of_maximal_descent
  intro i U hmax hU
  have h : CoverageCertificate.Classified U := by
    by_cases hi : i.val < 24
    · exact CoverageCertificate.classify_lower i hi U hmax
    · exact CoverageCertificate.classify_upper i (by omega) U hmax
  rcases h with hk | ⟨c, hc, hnc⟩ | hr
  · exact (hU.2 hk).elim
  · exact (hnc (hU.1 hc)).elim
  · exact hr

end Theory.GroupTheory.HeldM22A10.SecondExclusion.ForceNormalizer.Candidates
