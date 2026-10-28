module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.LocalControl
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalPrefixControl
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.RegularPaths
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.SourceCriticalApplications
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Iteration.Recurrence

/-!
# Regular paths and the exclusion of distance six from the source hypotheses

The proved natural-section theorem supplies the critical-prefix exclusion in
the orbit-escape calculation. Its two-clause critical-prefix control is also
available directly, including the already fixed displacement case. Thus the
regular-path construction and the distance-six contradiction have no remaining
local-control premise. Extended paths still use the independent prescribed
replacement theorem of (4.4.4).

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.1)--(4.4.4), pp.890--894.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.RegularSource
open PathCentrality.RegularPaths
open PathCentrality.RegularPaths.CommutatorPropagation
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

theorem criticalPrefixExclusion (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) :
    OrbitEscape.SourceCritical.CriticalPrefixExclusion R geometry := by
  intro a e p hn hnone
  have hl : 2 ≤ p.walk.length := by rw [p.length_eq_b]; omega
  exact hnone (hasNaturalSection_of_nonfixed common hb p.start_color
    ((p.vertex_color hl).mpr (by decide)) (p.dist_start hl) hn)

theorem criticalPrefixControl (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) : LocalCommutator.CriticalPrefixControl R geometry :=
  LocalCommutator.criticalPrefixControl_of_moving hb
    (critical_prefix_localControl common hb)

theorem orbitEscapeAlternative (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) {a e : Vertex R} (p : CriticalPath R geometry a e) :
    OrbitEscapeAlternative p :=
  orbitEscapeAlternative_of_criticalPrefix common hb (criticalPrefixExclusion common hb) p

theorem exists_regular (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) (a : Vertex R) (ha : color R a = false) :
    ∃ e, ∃ p : CriticalPath R geometry a e, HasTurnConjugators R p :=
  exists_regular_of_orbitEscape hb (orbitEscapeAlternative common hb) a ha

theorem six_lt (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) : 6 < geometry.b R := by
  obtain ⟨e, p, hp⟩ := exists_regular common hb (alpha R) rfl
  exact CommutatorPropagation.SourceCriticalApplications.six_lt
    common hb (criticalPrefixExclusion common hb) p hp

/-- The literal extended-path consumer retains only prescribed replacement. -/
theorem extended_of_replacement (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R)
    (replacement : ∀ {a e} (p : CriticalPath R geometry a e),
      HasTurnConjugators R p → PrescribedReplacement R p)
    (a : Vertex R) (ha : color R a = false) : Nonempty (ExtendedPath geometry a) :=
  Source44.RegularPaths.extended_of_replacement common hb
    (criticalPrefixExclusion common hb) replacement a ha

theorem terminal_seed (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) {a e : Vertex R}
    (p : CriticalPath R geometry a e) (hp : HasTurnConjugators R p)
    {t : Vertex R} (ht : Adjacent R a t)
    (hn : ¬ Z R e ≤ stabilizer R a ⊓
      normalizer (edgeCommutator R a t : Set (FreeAmalgam R)))
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R a)
    (hge : (edgeCommutator R a (p.walk.getVert 1)).map
      (MulAut.conj g⁻¹).toMonoidHom = edgeCommutator R a t)
    (hfail : (prescribedSpan p).map (MulAut.conj g⁻¹).toMonoidHom ≤
      Q R (p.walk.getVert (p.walk.length - 2))) :
    TerminalPropagationSeed p (failedSpanCommutator p g) :=
  CommutatorPropagation.SourceCriticalApplications.terminal_seed common hb
    (fun q => criticalPrefixExclusion common hb q) p hp ht hn hg hge hfail

theorem false_of_failed_span_and_backward_switching
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a e : Vertex R} (p : CriticalPath R geometry a e) (hp : HasTurnConjugators R p)
    {t : Vertex R} (ht : Adjacent R a t)
    (hn : ¬ Z R e ≤ stabilizer R a ⊓
      normalizer (edgeCommutator R a t : Set (FreeAmalgam R)))
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R a)
    (hge : (edgeCommutator R a (p.walk.getVert 1)).map
      (MulAut.conj g⁻¹).toMonoidHom = edgeCommutator R a t)
    (hfail : (prescribedSpan p).map (MulAut.conj g⁻¹).toMonoidHom ≤
      Q R (p.walk.getVert (p.walk.length - 2)))
    (hswitch : Iteration.BackwardEdgeSwitching p (failedSpanCommutator p g)) : False :=
  CommutatorPropagation.SourceCriticalApplications.false_of_failed_span_and_backward_switching
    common hb (fun q => criticalPrefixExclusion common hb q) p hp ht hn hg hge hfail hswitch

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.RegularSource
