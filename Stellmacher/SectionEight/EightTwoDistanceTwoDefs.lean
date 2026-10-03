module
public import Stellmacher.SectionEight.GeneratedContext

/-!
# The common subgroup in the distance-two case of (8.2)

The source subgroup V0 is the intersection of the initial neighbor-center
join Va with the two cores at its backward neighbor and first forward
neighbor. This definition retains the actual local graph and supplied
backward vertex, so the structure and Frattini arguments use the same
subgroup. Its centrality, normality, and index four require the distance-two
hypotheses and are proved separately.

The body is exposed intentionally: consumers calculate with the three
subgroup intersections in the source's V0 and its Frattini subgroup.
Source: Stellmacher (8.2), Journal of Algebra 190 (1997), printed p.38,
`refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.SectionEight
open Later

@[expose] public def distanceTwoVZero
    {G : Type*} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2) (back : ctx.Γ.Vertex) : Subgroup G :=
  VAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ back ⊓
    QAt ctx.Γ ctx.criticalPath.firstStep

end Stellmacher.SectionEight
