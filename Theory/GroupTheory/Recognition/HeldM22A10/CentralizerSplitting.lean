module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.FusionConstraints
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitModels
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.FirstExclusion
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.ThirdExclusion

/-!
# Splitting of the Held involution centralizer

The actual involution centralizer in a finite simple group satisfying
`LocalData` splits over its specified normal elementary abelian subgroup of
order sixteen. The local extension classification gives a complement or an
actual multiplicative equivalence to one of three concrete nonsplit groups.
The three ambient fusion exclusions eliminate all nonsplit alternatives.

`LocalData.exists_kernel_complement` discharges every intermediate premise
under the original local hypotheses, ambient finiteness and simplicity.
It proves the splitting clause of Huppert--Blackburn, *Finite Groups III*,
XII.1.18(b), printed p.314 (PDF p.322), citing D. Held, J. Algebra 8 (1968),
436--449, DOI 10.1016/0021-8693(68)90054-9, and Z. Janko, J. Algebra 9
(1968), 1--19 and 20--41. Global M22/A10 recognition is a separate conclusion.
-/

namespace Theory.GroupTheory.HeldM22A10.LocalData

universe u

/-- The involution centralizer splits over its specified elementary kernel,
under the original finite simple ambient-group hypotheses. -/
public theorem exists_kernel_complement
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G] (D : LocalData G) :
    ∃ K : Subgroup D.centralizer, D.kernel.IsComplement' K := by
  rcases nonsplitAlternatives D with h | h | h | h
  · exact h
  · exact (D.not_nonempty_equiv_first h).elim
  · exact (D.not_nonempty_equiv_second h).elim
  · exact (ThirdExclusion.not_nonempty_centralizer_equiv_third D h).elim

end Theory.GroupTheory.HeldM22A10.LocalData
