module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.BackwardChain
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.JointNormality.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.SourceCritical

/-!
# The local orbit-escape disjunction in MS93 (4.4.2)

If both local orbit spans remain in the indicated kernels, the first
subgroup argument makes their product normal in G_a. The backward critical
chain and the neighbor conjugator then give the R₁/R₂ contradiction.
This proves the disjunction opening (4.4.2), with the earlier local
commutator theorem retained as an explicit input. The regular-path
existence consumer remains in RegularPaths.Construction.

The separately named source-critical route replaces universal local control
by the earlier nonnatural exclusion restricted to genuine critical prefixes.
Its independent producer still has to discharge that premise.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.2), pp.892--893.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The escape alternative at the start of MS93 (4.4.2), with all
joint-normality, backward-chain, index and noncommutation inputs discharged. -/
theorem orbitEscapeAlternative
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (hlocal : LocalCommutatorControl R)
    {a a' : Vertex R} (p : CriticalPath R geometry a a') :
    OrbitEscapeAlternative p := by
  classical
  by_contra h
  have hfailure :
      localZSpan R (p.walk.getVert 2) a ≤ Q R (p.walk.getVert (p.walk.length - 2)) ∧
      ∀ g ∈ stabilizer R a, localZSpan R a (act R g (p.walk.getVert 2)) ≤
        Q R (p.walk.getVert (p.walk.length - 4)) := by
    simpa only [OrbitEscapeAlternative, not_or, not_not, not_exists, not_and] using h
  exact OrbitEscape.CommutatorContradiction.false_of_joint_normality
    common hb hlocal p hfailure.1 hfailure.2
    (OrbitEscape.JointNormality.jointSpan_normalized_of_failed_escape
      common hb hlocal p hfailure.1 hfailure.2)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths
