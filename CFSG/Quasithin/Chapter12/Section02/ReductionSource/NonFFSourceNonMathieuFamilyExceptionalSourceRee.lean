module
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.CubicSourceExclusionsReeComplete
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit

/-!
# Excluding the positive Ree marking of the literal chosen orbit component

The unconditional cubic-source exclusion applies to `D.orbitRepresentation`
and the central quotient of `D.orbitComponent`. The original ambient actors,
chosen module and quotient marking are exactly those of the family sieve.
This discharges its positive Ree branch; triality has a separate owner-local
proof obligation. Source: Aschbacher–Smith K.3, printed p.457/PDF468, citing
Guralnick–Malle II, Theorem 8.1/Table 17 and Lemma 8.8.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

theorem sourceOrbit_ree_cubic_false
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    {m : ℕ} (hm : 1 ≤ m)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* ReeF4.Model m)) : False :=
  ChapterK.Exceptional.CubicSourceExclusions.ree_cubic_source_false hs hm hq

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
