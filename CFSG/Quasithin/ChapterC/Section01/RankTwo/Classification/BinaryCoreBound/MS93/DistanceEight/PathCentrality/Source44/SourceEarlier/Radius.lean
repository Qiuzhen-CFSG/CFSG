module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.SourceEarlier.RadiusBoundary
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.Applications

/-!
# The full-radius natural section from the proved source prefix theorem

The large-image reduction and its distance-eight boundary now use only
critical-prefix control. The proved source theorem supplies that control,
so the actual quotient image has order two with no local-control premise.
The preceding second calculation then recognizes the full radius natural
section and its moving span, retaining the literal action and quotient.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.5), pp.894--895.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.SourceEarlier.Radius
open PathCentrality.FinalCalculation PathCentrality.FinalCalculation.RadiusImage
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The radius image in the actual local quotient has order at most two. -/
theorem source_image_le_two (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R)
    {a : Vertex R} (e : PathCentrality.RegularPaths.ExtendedPath geometry a) :
    (Q R (e.walk.getVert 4)).relIndex
      (V R (e.walk.getVert (2 + geometry.b R))) ≤ 2 := by
  by_contra hn
  have hprefix := prefix_control common (by omega : 4 < geometry.b R)
  obtain ⟨hb8,hfour,hE,_⟩ := RadiusReduction.large_image_reduction e common hb hprefix hn
  apply e.nonnormalization 8 (by decide) (by decide) (by decide)
  exact le_inf ((e.window 8 (by decide) (by decide)).endpoint_Z_le_start_stabilizer
    (by omega)) (RadiusBoundary.boundaryNormalization e common hprefix hb8 hfour hE)

/-- The source escape lower bound makes that same image have order two. -/
theorem source_image_eq_two (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R)
    {a : Vertex R} (e : PathCentrality.RegularPaths.ExtendedPath geometry a) :
    (Q R (e.walk.getVert 4)).relIndex
      (V R (e.walk.getVert (2 + geometry.b R))) = 2 :=
  le_antisymm (source_image_le_two common hb e) (ExtendedPath.two_le_source_image e common)

/-- Both local calculations construct the full natural radius section. -/
theorem natural_section (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R)
    {a : Vertex R} (e : PathCentrality.RegularPaths.ExtendedPath geometry a)
    {c : Vertex R} (hc : color R c = false) :
    Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c)) :=
  natural_section_of_source_image common hb (prefix_exclusion common (by omega)) e
    (source_image_le_two common hb e) hc

/-- The natural radius section gives the literal moving-span inclusion. -/
theorem moving_span (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R)
    {a : Vertex R} (e : PathCentrality.RegularPaths.ExtendedPath geometry a) :
    Vcirc R a ≤ localZSpan R (e.walk.getVert 2) a :=
  moving_span_of_source_image common hb (prefix_exclusion common (by omega)) e
    (source_image_le_two common hb e)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.SourceEarlier.Radius
