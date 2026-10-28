module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.JointNormality.LocalBounds.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.JointNormality.Selection

/-!
# Joint normality under failed orbit escape in MS93 (4.4.2)

The forward span V and reverse span V₁ have a product normal in the start
stabilizer whenever both escape alternatives fail. The relative normalizer
P of the edge commutator acts on V₁ to give the orbit span W. The actual
marked natural module supplies two separating edge conjugates. The local
commutator bounds show that, if V V₁ were not normal, the two nonzero displacement
groups H₁ and H₂ would fill the natural centralizer of the critical endpoint.
This puts the critical commutator in the terminal natural subgroup, contrary
to the final application of (4.4.1) and the supplied escape theorem (4.3).

This assembly discharges the selection and all three local bounds in the
conditional joint-normality theorem. Its only earlier-source inputs are
LocalSource, Geometry, CommonFacts and LocalCommutatorControl, with b > 4.
The second theorem states normality inside the actual start stabilizer;
`jointSpan_eq_product` identifies the join with the printed product.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.2), printed p.893, first subgroup argument. The parent orbit-escape
argument retains the subsequent R₁/R₂ contradiction and final disjunction.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.JointNormality

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R} {a a' : Vertex R}

/-- Failure of both source escape alternatives makes V V₁ invariant under G_a.
The two edge conjugates and every local displacement bound are constructed. -/
theorem jointSpan_normalized_of_failed_escape
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (hlocal : LocalCommutatorControl R) (p : CriticalPath R geometry a a')
    (hforward : localZSpan R (p.walk.getVert 2) a ≤
      Q R (p.walk.getVert (p.walk.length - 2)))
    (hreverse : ∀ g ∈ stabilizer R a,
      localZSpan R a (act R g (p.walk.getVert 2)) ≤
        Q R (p.walk.getVert (p.walk.length - 4))) :
    stabilizer R a ≤ normalizer (jointSpan p) :=
  LocalBounds.jointSpan_normalized_of_selection common hb hlocal p hforward hreverse
    (separatingConjugates common p)

/-- The printed product V V₁ is normal relative to G_a under failed escape. -/
theorem jointSpan_normal_of_failed_escape
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (hlocal : LocalCommutatorControl R) (p : CriticalPath R geometry a a')
    (hforward : localZSpan R (p.walk.getVert 2) a ≤
      Q R (p.walk.getVert (p.walk.length - 2)))
    (hreverse : ∀ g ∈ stabilizer R a,
      localZSpan R a (act R g (p.walk.getVert 2)) ≤
        Q R (p.walk.getVert (p.walk.length - 4))) :
    ((jointSpan p).subgroupOf (stabilizer R a)).Normal :=
  (jointSpan_normal_iff p common.large_distance).mpr
    (jointSpan_normalized_of_failed_escape common hb hlocal p hforward hreverse)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.JointNormality
