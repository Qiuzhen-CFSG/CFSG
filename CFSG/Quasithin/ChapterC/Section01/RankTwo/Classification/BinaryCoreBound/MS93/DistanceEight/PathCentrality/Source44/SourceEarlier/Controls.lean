module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.RegularSource

/-!
# The proved source controls for the final calculation of (4.4)

The source theorem constructs a natural section whenever the initial
displacement moves. Its critical-prefix specialization gives both local
control clauses; the fixed case follows directly by taking the local span.
These proved controls supply the regular-path construction and the strict
distance bound used by the final calculation. Prescribed replacement is the
remaining independent input, with its actual turns and endpoint markings.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1)--(4.4.5), pp.890--895.
-/
public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.SourceEarlier
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- Both local-control clauses hold on each actual source critical prefix. -/
theorem prefix_control (common : CommonFacts R source geometry) (hb : 4 < geometry.b R) :
    LocalCommutator.CriticalPrefixControl R geometry :=
  RegularSource.criticalPrefixControl common hb

/-- The source natural-section construction discharges the prefix exclusion. -/
theorem prefix_exclusion (common : CommonFacts R source geometry) (hb : 4 < geometry.b R) :
    PathCentrality.RegularPaths.OrbitEscape.SourceCritical.CriticalPrefixExclusion R geometry :=
  RegularSource.criticalPrefixExclusion common hb

/-- The regular extended path uses only the independent prescribed replacement. -/
theorem extended (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (replacement : ∀ {a a'} (p : CriticalPath R geometry a a'),
      HasTurnConjugators R p → PrescribedReplacement R p)
    (a : Vertex R) (ha : color R a = false) :
    Nonempty (PathCentrality.RegularPaths.ExtendedPath geometry a) :=
  RegularSource.extended_of_replacement common hb replacement a ha

/-- The actual first regular window excludes critical distance six. -/
theorem six_lt (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a : Vertex R} (e : PathCentrality.RegularPaths.ExtendedPath geometry a) :
    6 < geometry.b R :=
  PathCentrality.RegularPaths.CommutatorPropagation.SourceCriticalApplications.six_lt
    common hb (prefix_exclusion common hb) (e.window 0 (by decide) (by decide))
    (e.window_regular 0 (by decide) (by decide))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.SourceEarlier
