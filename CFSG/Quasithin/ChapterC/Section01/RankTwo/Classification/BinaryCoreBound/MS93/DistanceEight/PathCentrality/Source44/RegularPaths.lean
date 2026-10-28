module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.RegularPaths.Extension
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.SourceCritical
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.SourceIntegration

/-!
# Source regular-path assembly with the replacement obligation explicit

Critical-prefix exclusion supplies the original orbit escape and hence a
regular critical path. The variable-distance extension constructs all five
critical windows and all four nonnormalization clauses before the final
calculation determines b=8. The actual SourceIntegration consumer therefore
requires no independently supplied ExtendedPath.

Prescribed replacement is the remaining (4.4.4) source obligation. This module
does not assert its backward-edge switching step. Full local commutator control
and critical-prefix exclusion remain the genuine earlier (4.4.1) inputs.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.2)--(4.4.5), pp.892--894.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.RegularPaths
open PathCentrality.RegularPaths
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- Construct the literal extended path at each prescribed M-vertex using the
preceding regular-path theorem and prescribed replacement, without b=8. -/
theorem extended_of_replacement (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R)
    (exclude : OrbitEscape.SourceCritical.CriticalPrefixExclusion R geometry)
    (replacement : ∀ {a a'} (p : CriticalPath R geometry a a'),
      HasTurnConjugators R p → PrescribedReplacement R p)
    (a : Vertex R) (ha : color R a = false) : Nonempty (ExtendedPath geometry a) := by
  obtain ⟨a', p, hp⟩ := exists_regular_of_orbitEscape hb
    (fun p => orbitEscapeAlternative_of_criticalPrefix common hb exclude p) a ha
  exact extended_of_regular_and_replacement common hb.le replacement p hp a ha

/-- Literal final-calculation consumer: extended-path existence has been proved;
the source replacement theorem and its two genuine earlier controls remain. -/
theorem earlier_of_replacement (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) (hlocal : LocalCommutatorControl R)
    (exclude : OrbitEscape.SourceCritical.CriticalPrefixExclusion R geometry)
    (replacement : ∀ {a a'} (p : CriticalPath R geometry a a'),
      HasTurnConjugators R p → PrescribedReplacement R p) : CoreFactors.Earlier R geometry := by
  exact FinalCalculation.SourceIntegration.earlier common hb hlocal replacement exclude
    (extended_of_replacement common hb exclude replacement)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.RegularPaths
