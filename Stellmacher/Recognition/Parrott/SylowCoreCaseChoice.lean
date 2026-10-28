module

public import Stellmacher.Recognition.Parrott.SylowSeedFrame
public import Stellmacher.Recognition.Parrott.SylowCoreChoice

/-!
# The two cases of Parrott's core generators

Every supplied initial frame through (10) admits core generators satisfying
one of the two sets (11)–(15). The stronger `exists_core_relations` theorem
selects the correlated cosets, adjusts `a` by `t`, and corrects `c` by factors
from `⟨w,v,t,u⟩`. Here we expose its existence conclusion for seed assembly.
The resulting frame has the original normalizer data, so `z,t,v,F,T` and all
the initial equations and actual subgroup closure equalities are retained.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed p.679 and the opening of p.680. In Case 2, (15′) reads `[b,c] = ut`.
-/

namespace Stellmacher.Recognition.ParrottSylowInitialData

variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z}
variable {n : ParrottNormalizerFusionData e}

/-- Choose a frame satisfying either printed set of core relations, with the
supplied marked normalizer data and all equations through (10) preserved. -/
public theorem exists_core_case [Finite G] [IsSimpleGroup G]
    (f : ParrottSylowInitialData n) (hns : ¬ Group.IsSolvable G)
    (hN : IsNTwoGroup G) (h : ParrottCentralizerHypotheses z) :
    ∃ (caseTwo : Bool) (f' : ParrottSylowInitialData n), f'.CoreRelations caseTwo := by
  obtain ⟨caseTwo, f', hf', _⟩ := f.exists_core_relations hns hN h
  exact ⟨caseTwo, f', hf'⟩

end Stellmacher.Recognition.ParrottSylowInitialData
