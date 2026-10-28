module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.SourceCritical
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction.Configuration

/-!
# The genuine critical prefixes used by MS93 (4.4.2)

The earlier nonnatural-section exclusion is needed only at actual critical
prefixes. Reverse and conjugated critical paths give the local pairs in the
joint-normality argument. The reverse of the retained backward chain gives
the forward pair (a+2,a), including the application to the full actor
V_delta intersect Q_a in R₂.

These controls retain both clauses of (4.4.1), the original local spans and
the original actors. They do not assert local control on arbitrary orbits.
The exclusion is owned by LocalCommutator.CriticalCase and remains explicit.

Source: MS93 (4.4.1)--(4.4.2), printed pp.890--893.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.SourceCritical
open LocalCommutator
open LocalCommutator.NaturalCase.Opposite.Selection
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}

/-- Precisely the earlier nonnatural branch, restricted to genuine prefixes.
It assumes neither a local-control conclusion nor an orbit-escape theorem. -/
def CriticalPrefixExclusion (R : Subgroup M) (geometry : Geometry R) : Prop :=
  ∀ {d e : Vertex R} (p : CriticalPath R geometry d e),
    ¬ ⁅Z R d, Q R (p.walk.getVert 2)⁆ ≤ fixedCore R (p.walk.getVert 2) →
    ¬ HasNaturalSection R d (p.walk.getVert 2) → False

variable [Finite M] {source : LocalSource L R}

/-- Both local-control clauses at the actual initial pair of a critical path. -/
theorem prefix_control (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) (exclude : CriticalPrefixExclusion R geometry)
    {a e : Vertex R} (p : CriticalPath R geometry a e)
    (hn : ¬ ⁅Z R a, Q R (p.walk.getVert 2)⁆ ≤ fixedCore R (p.walk.getVert 2)) :
    LocalControlAt R a (p.walk.getVert 2) := by
  have htwo : 2 ≤ p.walk.length := by rw [p.length_eq_b]; omega
  exact LocalCommutator.SourceCritical.localControl_of_spanEscape common hb exclude
    p.start_color ((p.vertex_color htwo).mpr (by decide)) (p.dist_start htwo) hn
    (spanEscape_of_critical_prefix p (by omega))

/-- The pair (a′,a′−2) in the critical exclusion for joint normality. -/
theorem reverse_prefix_control (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) (exclude : CriticalPrefixExclusion R geometry)
    {a a' : Vertex R} (p : CriticalPath R geometry a a')
    (hn : ¬ ⁅Z R a', Q R (p.walk.getVert (p.walk.length - 2))⁆ ≤
      fixedCore R (p.walk.getVert (p.walk.length - 2))) :
    LocalControlAt R a' (p.walk.getVert (p.walk.length - 2)) := by
  have heq : (p.reverse common).walk.getVert 2 =
      p.walk.getVert (p.walk.length - 2) := SimpleGraph.Walk.getVert_reverse _ _
  have h := prefix_control common hb exclude (p.reverse common) (by rwa [heq])
  rwa [heq] at h

/-- The pair (a,(a+2)^g) for each actual stabilizer conjugator in (4.4.2). -/
theorem conjugate_prefix_control (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) (exclude : CriticalPrefixExclusion R geometry)
    {a a' : Vertex R} (p : CriticalPath R geometry a a')
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R a)
    (hn : ¬ ⁅Z R a, Q R (act R g (p.walk.getVert 2))⁆ ≤
      fixedCore R (act R g (p.walk.getVert 2))) :
    LocalControlAt R a (act R g (p.walk.getVert 2)) := by
  have hga : act R g a = a := hg
  have heq : (p.act g).walk.getVert 2 = act R g (p.walk.getVert 2) :=
    actWalk_getVert R g p.walk 2
  have h := prefix_control common hb exclude (p.act g) (by rwa [heq, hga])
  rwa [heq, hga] at h

/-- The forward pair (a+2,a) is a prefix of the reversed backward chain.
In particular both control clauses apply to the full R₂ actor, not just
to elements in a single Z-layer. -/
theorem backward_prefix_control (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) (exclude : CriticalPrefixExclusion R geometry)
    {a a' : Vertex R} {p : CriticalPath R geometry a a'}
    (s : CommutatorContradiction.Configuration p)
    (hn : ¬ ⁅Z R (p.walk.getVert 2), Q R a⁆ ≤ fixedCore R a) :
    LocalControlAt R (p.walk.getVert 2) a := by
  have hlen : s.chain.path.walk.length = p.walk.length :=
    s.chain.path.length_eq_b.trans p.length_eq_b.symm
  have heq : s.chain.path.walk.getVert (s.chain.path.walk.length - 2) = a := by
    rw [hlen]
    exact s.start_vertex hb
  have h := reverse_prefix_control common hb exclude s.chain.path
    (by rwa [heq, s.end_vertex hb])
  rwa [heq, s.end_vertex hb] at h

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.SourceCritical

