module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Seed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Iteration.Conclusion
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Iteration.TerminalDisplacement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.FullControl

/-!
# The failed-span consumer for prescribed replacement

Full local commutator control constructs the terminal seed and proves b > 6.
The backward switching contract then drives the four-step recurrence; its
terminal displacement is already proved. The resulting contradiction gives
prescribed-span escape, prescribed replacement, and the literal Earlier
consumer, with all original critical-path and inverse-conjugation data.

`FailedSpanSwitching` remains an explicit source obligation. This module
neither asserts that obligation nor substitutes a pointwise-centrality or
quadratic-action premise for it.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.4), printed p.894.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.Replacement
open PathCentrality.RegularPaths PathCentrality.RegularPaths.CommutatorPropagation
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

theorem false_of_failed_span
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (hlocal : LocalCommutatorControl R)
    {a a' : Vertex R} (p : CriticalPath R geometry a a')
    (hp : HasTurnConjugators R p)
    {t : Vertex R} (ht : Adjacent R a t)
    (hn : ¬ Z R a' ≤ stabilizer R a ⊓
      normalizer (edgeCommutator R a t : Set (FreeAmalgam R)))
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R a)
    (hge : (edgeCommutator R a (p.walk.getVert 1)).map
      (MulAut.conj g⁻¹).toMonoidHom = edgeCommutator R a t)
    (hfail : (prescribedSpan p).map (MulAut.conj g⁻¹).toMonoidHom ≤
      Q R (p.walk.getVert (p.walk.length - 2)))
    (hswitch : Iteration.BackwardEdgeSwitching p (failedSpanCommutator p g)) : False := by
  have hb6 := six_lt common hb hlocal p hp
  have seed := Seed.terminal_seed common p hb6 hlocal hp ht hn hg hge hfail
  exact Iteration.contradiction_of_local_steps common hb6 hlocal p hp seed hswitch
    (Iteration.terminal_displacement common p seed)

/-- The exact source switching obligation under failed prescribed-span escape. -/
@[expose] def FailedSpanSwitching (R : Subgroup M) (geometry : Geometry R) : Prop :=
  ∀ {a a'} (p : CriticalPath R geometry a a'), HasTurnConjugators R p →
    ∀ {t}, Adjacent R a t →
      ¬ Z R a' ≤ stabilizer R a ⊓
        normalizer (edgeCommutator R a t : Set (FreeAmalgam R)) →
      ∀ {g}, g ∈ stabilizer R a →
        (edgeCommutator R a (p.walk.getVert 1)).map (MulAut.conj g⁻¹).toMonoidHom =
          edgeCommutator R a t →
        (prescribedSpan p).map (MulAut.conj g⁻¹).toMonoidHom ≤
          Q R (p.walk.getVert (p.walk.length - 2)) →
        Iteration.BackwardEdgeSwitching p (failedSpanCommutator p g)

theorem spanEscape
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (hlocal : LocalCommutatorControl R)
    (hswitch : FailedSpanSwitching R geometry)
    {a a'} (p : CriticalPath R geometry a a') (hp : HasTurnConjugators R p) :
    PrescribedSpanEscape p := by
  intro t ht hn g hg hge hfail
  exact false_of_failed_span common hb hlocal p hp ht hn hg hge hfail
    (hswitch p hp ht hn hg hge hfail)

theorem prescribedReplacement
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (hlocal : LocalCommutatorControl R)
    (hswitch : FailedSpanSwitching R geometry)
    {a a'} (p : CriticalPath R geometry a a') (hp : HasTurnConjugators R p) :
    PrescribedReplacement R p :=
  prescribedReplacement_of_spanEscape p (by omega)
    (spanEscape common hb hlocal hswitch p hp)

theorem earlier
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (hlocal : LocalCommutatorControl R)
    (hswitch : FailedSpanSwitching R geometry) : CoreFactors.Earlier R geometry :=
  FullControl.earlier common hb hlocal
    (fun p hp => prescribedReplacement common hb hlocal hswitch p hp)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.Replacement
