module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Seed.Identification
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Seed.OrbitGrowth
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Seed.CriticalInclusion

/-!
# Construction of the terminal propagation seed in MS93 (4.4.4)

For a prescribed edge conjugator, suppose that the transported relative
P-orbit span lies in Q_(a'-2). The orbit growth argument proves that its
commutator R₀ with Z_a' is not contained in Z_a. The span contains the
selected incident edge, so R₀ contains the nonzero critical commutator.
The terminal edge's order bound then identifies R₀ with that edge.

Source (4.4.1) and the regular turns supply the fixed-core bound and first
backward edge equality. `Seed.terminal_seed` assembles all four assertions
from the source inputs, with the literal relative normalizer and inverse
conjugation. The subsequent backward iteration and prescribed-span escape
remain with the commutator-propagation assembly owner.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.4), printed p.894.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Seed
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The four initial R₀ assertions in MS93 (4.4.4), under failed escape of
the transported prescribed span. All intermediate P-orbit premises are discharged. -/
theorem terminal_seed (common : CommonFacts R source geometry)
    {a a' : Vertex R} (p : CriticalPath R geometry a a') (hb : 6 < geometry.b R)
    (hlocal : LocalCommutatorControl R) (hp : HasTurnConjugators R p)
    {t : Vertex R} (ht : Adjacent R a t)
    (hn : ¬ Z R a' ≤ stabilizer R a ⊓
      normalizer (edgeCommutator R a t : Set (FreeAmalgam R)))
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R a)
    (hge : (edgeCommutator R a (p.walk.getVert 1)).map
      (MulAut.conj g⁻¹).toMonoidHom = edgeCommutator R a t)
    (hfail : (prescribedSpan p).map (MulAut.conj g⁻¹).toMonoidHom ≤
      Q R (p.walk.getVert (p.walk.length - 2))) :
    TerminalPropagationSeed p (failedSpanCommutator p g) :=
  seed_of_critical_le common p hb hlocal hp hg hfail
    (OrbitGrowth.failedSpanCommutator_not_le_start_Z common p hn hg hge)
    (CriticalInclusion.critical_commutator_le_failedSpan common p ht hn hge)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Seed
