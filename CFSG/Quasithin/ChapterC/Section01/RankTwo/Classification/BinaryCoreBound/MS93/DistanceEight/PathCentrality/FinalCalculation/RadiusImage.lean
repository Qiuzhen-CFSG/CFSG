module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.RadiusImage.Reduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.RadiusImage.Boundary
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.Applications

/-!
# The first image calculation in MS93 (4.4.5)

The large-image reduction discharges the proper-edge branch and every b>8
case. The fixed-core calculation and residual turn in Boundary discharge
the b=8 full-edge case. Thus the literal radius image has order exactly two.
The actual NaturalSectionAt and moving-span consumers below use this
derived index; neither assumes an index or a full-radius natural section.

The earlier conditional wrappers are preserved. The final exports discharge
their boundary premise using the full LocalCommutatorControl. The independent
critical-prefix exclusion is used only for the second local calculation in
the natural-section and moving-span consumers. LocalCommutator and RegularPaths
retain their earlier-source obligations, whose discharge belongs to the
PathCentrality assembly and its DistanceEight parent.
Source: Meierfrankenfeld--Stellmacher (1993), (4.4.5), printed pp.894--895.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation.RadiusImage
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- All large-image branches reduce to the outstanding boundary normalization. -/
theorem source_image_le_two_of_boundary_normalization
    (common : CommonFacts R source geometry) (hb : 6 < geometry.b R)
    (hlocal : LocalCommutatorControl R)
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a)
    (hboundary : BoundaryNormalization e) :
    (Q R (e.walk.getVert 4)).relIndex
      (V R (e.walk.getVert (2 + geometry.b R))) ≤ 2 := by
  by_contra hn
  obtain ⟨hb8, hfour, hE, -⟩ := large_image_reduction e common hb hlocal hn
  apply e.nonnormalization 8 (by decide) (by decide) (by decide)
  exact le_inf ((e.window 8 (by decide) (by decide)).endpoint_Z_le_start_stabilizer
    (by omega)) (hboundary hb8 hfour hE)

/-- The common escape lower bound gives equality for the same literal image. -/
theorem source_image_eq_two_of_boundary_normalization
    (common : CommonFacts R source geometry) (hb : 6 < geometry.b R)
    (hlocal : LocalCommutatorControl R)
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a)
    (hboundary : BoundaryNormalization e) :
    (Q R (e.walk.getVert 4)).relIndex
      (V R (e.walk.getVert (2 + geometry.b R))) = 2 :=
  le_antisymm (source_image_le_two_of_boundary_normalization common hb hlocal e hboundary)
    (ExtendedPath.two_le_source_image e common)

/-- Actual full-radius recognition after the boundary calculation. The earlier
critical-prefix exclusion supplies the already proved second local calculation. -/
theorem natural_section_of_boundary_normalization
    (common : CommonFacts R source geometry) (hb : 6 < geometry.b R)
    (hlocal : LocalCommutatorControl R)
    (exclude : ∀ {d f : Vertex R} (p : CriticalPath R geometry d f),
      ¬ ⁅Z R d, Q R (p.walk.getVert 2)⁆ ≤ fixedCore R (p.walk.getVert 2) →
      ¬ LocalCommutator.HasNaturalSection R d (p.walk.getVert 2) → False)
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a)
    (hboundary : BoundaryNormalization e)
    {c : Vertex R} (hc : color R c = false) :
    Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c)) :=
  natural_section_of_source_image common hb exclude e
    (source_image_le_two_of_boundary_normalization common hb hlocal e hboundary) hc

/-- Apply the derived index to the literal alpha-2 moving-span consumer. -/
theorem moving_span_of_boundary_normalization
    (common : CommonFacts R source geometry) (hb : 6 < geometry.b R)
    (hlocal : LocalCommutatorControl R)
    (exclude : ∀ {d f : Vertex R} (p : CriticalPath R geometry d f),
      ¬ ⁅Z R d, Q R (p.walk.getVert 2)⁆ ≤ fixedCore R (p.walk.getVert 2) →
      ¬ LocalCommutator.HasNaturalSection R d (p.walk.getVert 2) → False)
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a)
    (hboundary : BoundaryNormalization e) :
    Vcirc R a ≤ localZSpan R (e.walk.getVert 2) a :=
  moving_span_of_source_image common hb exclude e
    (source_image_le_two_of_boundary_normalization common hb hlocal e hboundary)

/-- The first local calculation of (4.4.5), including the full-edge b=8 case.
Only the earlier local commutator control and the actual extended path are inputs. -/
theorem source_image_le_two
    (common : CommonFacts R source geometry) (hb : 6 < geometry.b R)
    (hlocal : LocalCommutatorControl R)
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a) :
    (Q R (e.walk.getVert 4)).relIndex
      (V R (e.walk.getVert (2 + geometry.b R))) ≤ 2 :=
  source_image_le_two_of_boundary_normalization common hb hlocal e
    (Boundary.boundaryNormalization e common hlocal)

/-- The actual image V_(alpha'-2)Q_alpha/Q_alpha has order exactly two. -/
theorem source_image_eq_two
    (common : CommonFacts R source geometry) (hb : 6 < geometry.b R)
    (hlocal : LocalCommutatorControl R)
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a) :
    (Q R (e.walk.getVert 4)).relIndex
      (V R (e.walk.getVert (2 + geometry.b R))) = 2 :=
  le_antisymm (source_image_le_two common hb hlocal e)
    (ExtendedPath.two_le_source_image e common)

/-- Apply both source local calculations to construct the actual full-radius
natural section. The first image bound is discharged here. -/
theorem natural_section
    (common : CommonFacts R source geometry) (hb : 6 < geometry.b R)
    (hlocal : LocalCommutatorControl R)
    (exclude : ∀ {d f : Vertex R} (p : CriticalPath R geometry d f),
      ¬ ⁅Z R d, Q R (p.walk.getVert 2)⁆ ≤ fixedCore R (p.walk.getVert 2) →
      ¬ LocalCommutator.HasNaturalSection R d (p.walk.getVert 2) → False)
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a)
    {c : Vertex R} (hc : color R c = false) :
    Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c)) :=
  natural_section_of_source_image common hb exclude e
    (source_image_le_two common hb hlocal e) hc

/-- The derived image bound supplies the literal alpha-2 moving-span consumer. -/
theorem moving_span
    (common : CommonFacts R source geometry) (hb : 6 < geometry.b R)
    (hlocal : LocalCommutatorControl R)
    (exclude : ∀ {d f : Vertex R} (p : CriticalPath R geometry d f),
      ¬ ⁅Z R d, Q R (p.walk.getVert 2)⁆ ≤ fixedCore R (p.walk.getVert 2) →
      ¬ LocalCommutator.HasNaturalSection R d (p.walk.getVert 2) → False)
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a) :
    Vcirc R a ≤ localZSpan R (e.walk.getVert 2) a :=
  moving_span_of_source_image common hb exclude e
    (source_image_le_two common hb hlocal e)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation.RadiusImage
