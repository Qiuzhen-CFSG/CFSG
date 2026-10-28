module
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.CubicSourceExclusionsTrialityComplete
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit

/-!
# Excluding the triality marking of the literal chosen orbit component

The complete cubic-source exclusion applies to `D.orbitRepresentation` and
the central quotient of `D.orbitComponent`, with the original ambient actors
and every positive binary exponent. This discharges the triality branch of
the non-Mathieu family sieve. Source: Aschbacher--Smith K.3, p.457/PDF468,
citing Guralnick--Malle II, Theorem 8.1/Table 17 and Lemma 8.6.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

theorem sourceOrbit_triality_cubic_false
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    {r : ℕ} (hr : 1 ≤ r)
    (hq : Triality.Standard.IsTrialityGroupAt (2 ^ r)
      (D.orbitComponent ⧸ center D.orbitComponent)) : False :=
  ChapterK.Exceptional.CubicSourceExclusions.triality_cubic_source_false hs hr hq

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
