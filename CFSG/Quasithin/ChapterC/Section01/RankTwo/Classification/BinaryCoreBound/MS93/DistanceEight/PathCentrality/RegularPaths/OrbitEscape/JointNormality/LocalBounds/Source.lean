module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.JointNormality.LocalBounds.Seed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.JointNormality

/-!
# The three local bounds in MS93 (4.4.2)

The single-seed calculations extend to the actual P-orbit span by the
commutator-preimage argument. Together with the critical exclusion from
(4.4.1) and (4.3), they discharge all three local inputs in the first
joint-normality argument. Only forward failed escape is needed for these
bounds; reverse failed escape enters the subsequent joint-normality assembly.

The final theorem applies these bounds to the existing joint-normality
consumer. Selection of the two separating edge conjugates remains explicit
and belongs to the parent source assembly. All groups, relative normalizers
and inverse conjugations are the literal ones in JointNormality.Reduction.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.2), printed p.893, first subgroup argument.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.JointNormality.LocalBounds

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R} {a a' : Vertex R}

/-- The contained displacement, edge displacement and critical exclusion
under the source inputs, with both seed premises discharged. -/
theorem local_bounds (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) (hlocal : LocalCommutatorControl R)
    (p : CriticalPath R geometry a a')
    (hforward : localZSpan R (p.walk.getVert 2) a ≤
      Q R (p.walk.getVert (p.walk.length - 2))) :
    ContainedDisplacementBound p ∧ EdgeDisplacementBound p ∧
      ¬ ⁅Z R a, Z R a'⁆ ≤ U R (p.walk.getVert (p.walk.length - 2)) :=
  local_bounds_of_seed common hb hlocal p
    (Seed.containedSeedBound common hb p hforward)
    (Seed.edgeSeedBound common hb hlocal p hforward)

/-- Apply the three proved local bounds to the actual joint span. The parent
assembly must supply the independent separating-conjugate selection. -/
theorem jointSpan_normalized_of_selection (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) (hlocal : LocalCommutatorControl R)
    (p : CriticalPath R geometry a a')
    (hforward : localZSpan R (p.walk.getVert 2) a ≤
      Q R (p.walk.getVert (p.walk.length - 2)))
    (hreverse : ∀ g ∈ stabilizer R a,
      localZSpan R a (act R g (p.walk.getVert 2)) ≤
        Q R (p.walk.getVert (p.walk.length - 4)))
    (hselect : SeparatingConjugates p) :
    stabilizer R a ≤ normalizer (jointSpan p) := by
  obtain ⟨hcontained, hedge, hexclude⟩ := local_bounds common hb hlocal p hforward
  exact jointSpan_normalized_of_source_steps common p hb hreverse hselect
    hcontained hedge hexclude

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.JointNormality.LocalBounds
