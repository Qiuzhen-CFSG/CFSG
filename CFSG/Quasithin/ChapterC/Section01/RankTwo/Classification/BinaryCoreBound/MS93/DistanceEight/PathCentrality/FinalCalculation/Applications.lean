module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.LocalBounds
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.Recognition
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Terminal.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.Numerical.SourceCenterBound.DistanceGreaterFour.FixedFactor

/-!
# The radius section and numerical consumer of the final calculation

The proved R1 containment and an upper bound of two for the literal source
image V_(alpha'-2)Q_alpha/Q_alpha give c(V_(alpha'-2)/Z_(alpha'-2))=1.
Actual vertex conjugation transports all fields to the chosen center. The
backward critical window then supplies a genuine moving neighbor, so its
local Z-span contains Vcirc_alpha. Together with the still explicit local
centrality this gives the numerical bound |H_alpha|<=4.

The image bound is the first paragraph of (4.4.5), p.894, and remains a source
obligation. The later local centrality is the final argument on p.895. Neither
is assumed to be a proved source theorem by this conditional application.
The earlier critical-prefix exclusion and extended path belong to the
LocalCommutator and RegularPaths producers; final discharge belongs to the
PathCentrality assembly and its DistanceEight parent.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

omit [Finite M] in
/-- Transport the full section, including the actual projection and action,
between two M-type vertices. -/
theorem natural_section_at_any_center {v c : Vertex R}
    (hv : color R v = false) (hc : color R c = false)
    (s : Escape.NaturalSectionAt v (V R v) (Z R v)) :
    Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c)) := by
  obtain ⟨g, hg⟩ := exists_mVertex_of_color R hv
  obtain ⟨h, hh⟩ := exists_mVertex_of_color R hc
  have he : act R (g⁻¹ * h) v = c := by
    rw [hg, act_mVertex, mul_inv_cancel_left, ← hh]
  have s' := LocalCommutator.CriticalCase.naturalSectionAt_act (g⁻¹ * h) s
  rw [← V_act, ← Z_act, he] at s'
  exact ⟨s'⟩

/-- Apply the second (4.4.5) calculation and actual quotient recognition.
Only its first image bound remains beyond the preceding source inputs. -/
theorem natural_section_of_source_image
    (common : CommonFacts R source geometry) (hb : 6 < geometry.b R)
    (exclude : ∀ {d f : Vertex R} (p : CriticalPath R geometry d f),
      ¬ ⁅Z R d, Q R (p.walk.getVert 2)⁆ ≤ fixedCore R (p.walk.getVert 2) →
      ¬ LocalCommutator.HasNaturalSection R d (p.walk.getVert 2) → False)
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a)
    (himage : (Q R (e.walk.getVert 4)).relIndex
      (V R (e.walk.getVert (2 + geometry.b R))) ≤ 2)
    {c : Vertex R} (hc : color R c = false) :
    Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c)) := by
  obtain ⟨s⟩ := natural_section_of_critical_hyperplane common
    (e.window 2 (by decide) (by decide)) himage
    (ExtendedPath.firstCommutator_le_critical e common hb exclude)
  exact natural_section_at_any_center (e.window 2 (by decide) (by decide)).end_color hc s

/-- The genuine alpha-2 span contains the moving radius subgroup at alpha. -/
theorem moving_span_of_source_image
    (common : CommonFacts R source geometry) (hb : 6 < geometry.b R)
    (exclude : ∀ {d f : Vertex R} (p : CriticalPath R geometry d f),
      ¬ ⁅Z R d, Q R (p.walk.getVert 2)⁆ ≤ fixedCore R (p.walk.getVert 2) →
      ¬ LocalCommutator.HasNaturalSection R d (p.walk.getVert 2) → False)
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a)
    (himage : (Q R (e.walk.getVert 4)).relIndex
      (V R (e.walk.getVert (2 + geometry.b R))) ≤ 2) :
    Vcirc R a ≤ localZSpan R (e.walk.getVert 2) a := by
  obtain ⟨s⟩ := natural_section_of_source_image common hb exclude e himage
    (ExtendedPath.center_color e)
  rw [localZSpan_eq_conjugates]
  exact Escape.Initial.Natural.moving_generation_of_naturalSection
    source geometry common.large_distance a (ExtendedPath.center_color e) s _
    (ExtendedPath.backward_moving e source common.large_distance)

/-- Actual application to the numerical fixed-factor consumer. The image bound
and the later source centrality remain explicit assembly obligations. -/
theorem H_card_le_four_of_source_image
    (common : CommonFacts R source geometry) (hb : 6 < geometry.b R)
    (exclude : ∀ {d f : Vertex R} (p : CriticalPath R geometry d f),
      ¬ ⁅Z R d, Q R (p.walk.getVert 2)⁆ ≤ fixedCore R (p.walk.getVert 2) →
      ¬ LocalCommutator.HasNaturalSection R d (p.walk.getVert 2) → False)
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a)
    (himage : (Q R (e.walk.getVert 4)).relIndex
      (V R (e.walk.getVert (2 + geometry.b R))) ≤ 2)
    (hc : ⁅V R a, Q R a⁆ ≤
      (center (stabilizer R a)).map (stabilizer R a).subtype) :
    Nat.card (H R a) ≤ 4 :=
  Numerical.SourceCenterBound.DistanceGreaterFour.H_card_le_four_of_moving_span
    common (ExtendedPath.center_color e) (ExtendedPath.backward_distance e)
    (moving_span_of_source_image common hb exclude e himage) hc

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation
