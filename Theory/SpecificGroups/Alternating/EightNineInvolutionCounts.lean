module

public import Theory.SpecificGroups.Alternating.EightNineInvolutionCounts.EightCount
public import Theory.SpecificGroups.Alternating.EightNineInvolutionCounts.NineCount

/-!
# Mixed involution-pair counts in the actual alternating groups A₈ and A₉

For z = (01)(23)(45)(67) and t = (01)(23), the fiber of the half-order
power over z in A₈ has 156 ordered pairs, and the fiber over t in A₉ has
555. The latter centralizer has order 480. The computation first restricts
both factors to the centralizer, whose complete small table is certified
using its structural order formula. Odd commuting permutations identify
the relevant alternating conjugacy classes with their cycle types.

Source motivation: Aschbacher, “A 2-local characterization of M12”,
Proposition 3.3, printed p.38. All table data and numerical counts are checked
by the Lean kernel; `source/Generate.py` only reproduces candidate data.
-/
