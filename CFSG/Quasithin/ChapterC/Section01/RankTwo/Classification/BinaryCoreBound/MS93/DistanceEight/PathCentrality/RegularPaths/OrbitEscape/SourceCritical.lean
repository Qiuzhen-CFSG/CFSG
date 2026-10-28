module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.SourceCritical.JointNormality
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.SourceCritical.IndexTwo
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.SourceCritical.SecondCommutator

/-!
# Orbit escape from the source critical-prefix calculation

Failure of both alternatives gives joint normality using the reversed
critical path and the actual conjugated prefixes. The retained backward
chain supplies the forward local pair. Its R₁ calculation proves index two
and the independent conjugate noncommutation; the R₂ calculation then
forces the literal second commutator both inside and outside Z_delta D_delta.

The only earlier local-calculation premise is CriticalPrefixExclusion,
the nonnatural branch of (4.4.1) on genuine critical prefixes. Its independent
producer is LocalCommutator.CriticalCase. That premise must be discharged
before claiming a theorem from LocalSource and CommonFacts alone. Neither
universal local control nor arbitrary-orbit escape is asserted here.

Source: MS93 (4.4.2), printed pp.892--893.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The full failed-escape contradiction on the actual backward configuration.
The source-critical joint-normality, index-two and noncommutation producers
discharge all intermediate premises. -/
theorem OrbitEscape.SourceCritical.false_of_failed_escape
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (exclude : OrbitEscape.SourceCritical.CriticalPrefixExclusion R geometry)
    {a a' : Vertex R} (p : CriticalPath R geometry a a')
    (hforward : localZSpan R (p.walk.getVert 2) a ≤
      Q R (p.walk.getVert (p.walk.length - 2)))
    (hreverse : ∀ g ∈ stabilizer R a,
      localZSpan R a (act R g (p.walk.getVert 2)) ≤
        Q R (p.walk.getVert (p.walk.length - 4))) : False := by
  have hnormal := OrbitEscape.JointNormality.SourceCritical.jointSpan_normalized_of_failed_escape
    common hb exclude p hforward hreverse
  obtain ⟨s⟩ := OrbitEscape.CommutatorContradiction.exists_configuration common p hb hnormal
  obtain ⟨hindex, hmove⟩ :=
    s.backward_index_two_and_conjugate_noncommutation_of_criticalPrefix hb common exclude hnormal
  exact s.false_of_index_two_and_conjugate_noncommutation_of_criticalPrefix
    hb common exclude hforward hreverse hnormal hindex hmove

/-- The source-sufficient route to the disjunction opening MS93 (4.4.2).
Only the earlier nonnatural exclusion on critical prefixes remains explicit;
all orbit-escape subgroup arguments are proved on the original path. -/
theorem orbitEscapeAlternative_of_criticalPrefix
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (exclude : OrbitEscape.SourceCritical.CriticalPrefixExclusion R geometry)
    {a a' : Vertex R} (p : CriticalPath R geometry a a') :
    OrbitEscapeAlternative p := by
  classical
  by_contra h
  have hfailure :
      localZSpan R (p.walk.getVert 2) a ≤ Q R (p.walk.getVert (p.walk.length - 2)) ∧
      ∀ g ∈ stabilizer R a, localZSpan R a (act R g (p.walk.getVert 2)) ≤
        Q R (p.walk.getVert (p.walk.length - 4)) := by
    simpa only [OrbitEscapeAlternative, not_or, not_not, not_exists, not_and] using h
  exact OrbitEscape.SourceCritical.false_of_failed_escape
    common hb exclude p hfailure.1 hfailure.2

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths

