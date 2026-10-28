module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Consequences
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Propagation.Algebra
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Propagation.Actors
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Propagation.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Propagation.Cyclic

/-!
# Propagating the local seed and retaining the natural marking

The local seed determines the full midpoint orbit span inside Q_c and a
marked cyclic vector in its actual quotient by Z_alpha. Geometry proves
containment using the full-parabolic factorization M = P₁ P₂ P₁: the
midpoint-line preimage is normalized by P₁, its P₂-span is the seed, and
V_alpha ∩ Q_c is normalized by P₁. Cyclic transports the midpoint line
and seed plane to the orbit quotient and aligns both parabolics with the
dual twist of exactly common.natural.marking.

This gives the propagation and marked cyclic output of MS93 (1993),
(4.6.12)(3), printed pp.910–911, with the actual flag geometry of p.905
and quotient needed on p.912. The parabolic argument replaces the printed
delta3–delta4 propagation and base Q_delta2 generation step, whose literal
formula is disproved in Actors. The conditional displaced-core reduction
in Algebra is preserved but is not needed for this proof.

LocalConsequences remains an explicit intermediate input. Its construction
from the original seed and final assembly of source clause (3) belong to
the Seed owner. No whole-span containment or cyclic witness is assumed here.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Seed

variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The local seed propagates to the full midpoint span and supplies a cyclic
vector with the prescribed dual marking in its genuine quotient. The distance,
large-intersection and adjacency hypotheses are retained from the source branch;
their local consequences suffice for the propagation itself. -/
theorem propagation_of_local [Finite M]
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (_hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (_hs : ¬ s.SmallIntersection) (_hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Frame source)
    (hf : Compatible f s) (x : Input (geometry := geometry) d f s.middle)
    (hlocal : LocalConsequences d f s.middle x) :
    orbitSpan s.middle ≤ Q R s.middle ∧
      ∃ dO : LayerModule source (orbitSpan s.middle),
        Nonempty (MarkedCyclicSeed common s.middle dO) := by
  obtain ⟨dO⟩ := exists_orbitModule common radius s
  exact ⟨orbitSpan_le_kernel_of_local common hlocal s.first_distance,
    dO, exists_markedCyclicSeed common radius s hf hlocal dO⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Seed
