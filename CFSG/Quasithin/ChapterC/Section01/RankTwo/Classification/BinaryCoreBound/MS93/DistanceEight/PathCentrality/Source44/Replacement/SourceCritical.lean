module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.LocalControl
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.Replacement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.Replacement.RadiusImage
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.SourceCriticalApplications

/-!
# Prescribed replacement from the actual critical-prefix source control

The proved natural-section theorem rules out the nonnatural critical-prefix
case. This supplies every local-control use in the source-specific terminal
seed and contradiction, without universal control on arbitrary pairs.
Backward switching then gives prescribed replacement on the literal regular
critical path. The final consumer uses the radius-image reduction, so only
normalization of an escaping image of order two is left explicit.

Neither switching nor its residual normalization is asserted here. The
original failed span, prescribed edge, local conjugator, and path turns are
retained in that remaining source contract.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1)--(4.4.4), pp.890--894.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.Replacement.SourceCritical
open PathCentrality.RegularPaths PathCentrality.RegularPaths.CommutatorPropagation
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem exclude (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {d e : Vertex R} (p : CriticalPath R geometry d e)
    (hn : ¬ ⁅Z R d,Q R (p.walk.getVert 2)⁆ ≤ fixedCore R (p.walk.getVert 2))
    (hnot : ¬ LocalCommutator.HasNaturalSection R d (p.walk.getVert 2)) : False := by
  have hlen : 2 ≤ p.walk.length := by rw [p.length_eq_b]; omega
  exact hnot (Source44.hasNaturalSection_of_nonfixed common hb p.start_color
    ((p.vertex_color hlen).mpr (by decide)) (p.dist_start hlen) hn)

theorem spanEscape (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (hswitch : FailedSpanSwitching R geometry)
    {a a'} (p : CriticalPath R geometry a a') (hp : HasTurnConjugators R p) :
    PrescribedSpanEscape p := by
  intro t ht hn g hg hge hfail
  exact SourceCriticalApplications.false_of_failed_span_and_backward_switching
    common hb (exclude common hb) p hp ht hn hg hge hfail
    (hswitch p hp ht hn hg hge hfail)

theorem prescribedReplacement (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) (hswitch : FailedSpanSwitching R geometry)
    {a a'} (p : CriticalPath R geometry a a') (hp : HasTurnConjugators R p) :
    PrescribedReplacement R p :=
  prescribedReplacement_of_spanEscape p (by omega) (spanEscape common hb hswitch p hp)

/-- The remaining image-two normalization under the original failed-span inputs. -/
@[expose] def FailedSpanTwoImageNormalization (R : Subgroup M) (geometry : Geometry R) : Prop :=
  ∀ {a a'} (p : CriticalPath R geometry a a'), HasTurnConjugators R p →
    ∀ {t}, Adjacent R a t →
      ¬ Z R a' ≤ stabilizer R a ⊓
        normalizer (edgeCommutator R a t : Set (FreeAmalgam R)) →
      ∀ {g}, g ∈ stabilizer R a →
        (edgeCommutator R a (p.walk.getVert 1)).map (MulAut.conj g⁻¹).toMonoidHom =
          edgeCommutator R a t →
        (prescribedSpan p).map (MulAut.conj g⁻¹).toMonoidHom ≤
          Q R (p.walk.getVert (p.walk.length - 2)) →
        BackwardTwoImageNormalization p (failedSpanCommutator p g)

theorem switching_of_two_image_normalized (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) (hnorm : FailedSpanTwoImageNormalization R geometry) :
    FailedSpanSwitching R geometry := by
  intro a a' p hp t ht hn g hg hge hfail
  have seed := SourceCriticalApplications.terminal_seed common hb (exclude common hb)
    p hp ht hn hg hge hfail
  exact backwardEdgeSwitching_of_two_image_normalized common p hg seed
    (hnorm p hp ht hn hg hge hfail)

theorem prescribedReplacement_of_two_image_normalized
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (hnorm : FailedSpanTwoImageNormalization R geometry)
    {a a'} (p : CriticalPath R geometry a a') (hp : HasTurnConjugators R p) :
    PrescribedReplacement R p :=
  prescribedReplacement common hb (switching_of_two_image_normalized common hb hnorm) p hp

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.Replacement.SourceCritical
