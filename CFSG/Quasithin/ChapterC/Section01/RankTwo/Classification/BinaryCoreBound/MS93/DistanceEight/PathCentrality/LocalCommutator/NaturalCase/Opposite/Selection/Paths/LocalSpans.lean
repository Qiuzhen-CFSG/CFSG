module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.Paths.LocalSpans.Coordinates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.Paths.LocalSpans.BadImage
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.Paths.LocalSpans.GoodImage
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.Paths.Geometry

/-!
# Lifting the local conjugate-span calculations to the source path selection

The coordinate calculations have two different purposes. A proper
image of the bad conjugates together with the incident radius group proves
the displayed nonspanning assertion and supplies a good conjugate. A full
image of the good product intersected with Z_c[W,G_c] lifts across its proved
kernel Z_c. The good conjugate then supplies the rest of W.

These results apply to the original inverse-conjugated edge and the original
frame projection and markings. The final theorem feeds the literal cover to
Paths.Geometry.pathPlacement_of_spanEscape_and_cover. BadImage supplies the
proper image from the incident natural geometry; GoodImage then constructs
the full moving image using differences of good and incident conjugates.
Both coordinate premises are discharged below, proving the bad-span estimate
and the sufficient good-span cover from the supplied opposite frame and edge.
Only the independent orbit escape remains explicit in the path application;
its producer and the unconditional path assembly belong to the path owner.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1)(1), printed pp.890–891,
the bad-conjugate span multiplied by V_(alpha+3).
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection
open LocalSpans
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
variable {geometry : Geometry R} {a c u : Vertex R}

/-- Properness in the actual marked quotient gives the source bad-span estimate. -/
theorem localZSpan_not_le_badConjugateSpan_sup_radius_of_coordinates
    (source : LocalSource L R) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (hb : 2 < geometry.b R)
    (f : FrameAt a c) (hop : ¬ f.SameOrientation) (s : EdgeData a c)
    (hcu : Adjacent R c u)
    (hbad : coordinateImage source hc hd hb f hop (badConjugateSpan a c s.neighbor u) ⊔
      coordinateImage source hc hd hb f hop (V R u) ≠ ⊤) :
    ¬ localZSpan R a c ≤ badConjugateSpan a c s.neighbor u ⊔ V R u := by
  apply not_le_of_coordinateImage_ne_top source hc hd hb f hop
  rwa [coordinateImage_join_radius source hc hd hb f hop hcu _
    (badConjugateSpan_le a c s.neighbor u)]

/-- The full good image lifts on the moving preimage, whose exact kernel is Z_c.
The bad estimate supplies a good conjugate for the remaining fixed summand. -/
theorem localZSpan_le_goodConjugateSpan_sup_radius_of_coordinates
    (source : LocalSource L R) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (hb : 2 < geometry.b R)
    (f : FrameAt a c) (hop : ¬ f.SameOrientation) (s : EdgeData a c)
    (hcu : Adjacent R c u)
    (hbad : coordinateImage source hc hd hb f hop (badConjugateSpan a c s.neighbor u) ⊔
      coordinateImage source hc hd hb f hop (V R u) ≠ ⊤)
    (hgood : coordinateImage source hc hd hb f hop
      ((goodConjugateSpan a c s.neighbor u ⊔ V R u) ⊓ movingSpan a c) = ⊤) :
    localZSpan R a c ≤ goodConjugateSpan a c s.neighbor u ⊔ V R u := by
  classical
  have hex : ∃ g : stabilizer R c, GoodConjugate a c s.neighbor u g := by
    by_contra! h
    apply localZSpan_not_le_badConjugateSpan_sup_radius_of_coordinates
      source hc hd hb f hop s hcu hbad
    apply le_trans (b := badConjugateSpan a c s.neighbor u) _ le_sup_left
    exact iSup_le fun g => le_iSup_of_le g (le_iSup_of_le (h g) le_rfl)
  have hZ : Z R c ≤ goodConjugateSpan a c s.neighbor u ⊔ V R u := by
    apply le_trans (b := V R u) _ le_sup_right
    apply le_iSup_of_le c
    exact le_iSup_of_le (show (cosetGraph R).dist c u ≤ 2 from
      (SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hcu)).le.trans
        (by decide)) le_rfl
  exact (span_le_moving_sup_good hex).trans
    (sup_le (movingSpan_le_of_coordinateImage source hc hd hb f hop s _ hZ hgood) le_sup_left)

/-- Actual application to the built geometric assembly. Orbit escape and both
finite-image calculations must still be supplied by their source producers. -/
theorem pathPlacement_of_spanEscape_and_coordinate_estimates
    (source : LocalSource L R) (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (hb : 4 < geometry.b R)
    (f : FrameAt a c) (hop : ¬ f.SameOrientation) (s : EdgeData a c)
    (escape : SpanEscape geometry a c)
    (hbad : ∀ u : Vertex R, Adjacent R c u →
      coordinateImage source hc hd (show 2 < geometry.b R from by omega) f hop (badConjugateSpan a c s.neighbor u) ⊔
        coordinateImage source hc hd (show 2 < geometry.b R from by omega) f hop (V R u) ≠ ⊤)
    (hgood : ∀ u : Vertex R, Adjacent R c u →
      coordinateImage source hc hd (show 2 < geometry.b R from by omega) f hop
        ((goodConjugateSpan a c s.neighbor u ⊔ V R u) ⊓ movingSpan a c) = ⊤) :
    Nonempty (PathPlacement geometry a c s.neighbor) := by
  apply pathPlacement_of_spanEscape_and_cover ha hc hb s.toMovingSeed escape
  intro u hcu
  exact localZSpan_le_goodConjugateSpan_sup_radius_of_coordinates
    source hc hd (show 2 < geometry.b R from by omega) f hop s hcu (hbad u hcu) (hgood u hcu)

/-- The source's displayed bad-conjugate nonspanning assertion, including
the incident radius factor and the original inverse-conjugated edge.
The incident pairing and order-four displacement are supplied by BadImage. -/
theorem localZSpan_not_le_badConjugateSpan_sup_radius
    (source : LocalSource L R) (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    (hn : ¬ ⁅Z R a, Q R c⁆ ≤ fixedCore R c)
    (f : FrameAt a c) (hop : ¬ f.SameOrientation) (s : EdgeData a c)
    (hcu : Adjacent R c u) :
    ¬ localZSpan R a c ≤ badConjugateSpan a c s.neighbor u ⊔ V R u :=
  localZSpan_not_le_badConjugateSpan_sup_radius_of_coordinates
    source hc hd (by omega) f hop s hcu
    (bad_coordinate_image_sup_radius_ne_top common hb ha hc hd hn f hop s hcu)

/-- The good original conjugates and the incident radius cover the whole
local span. GoodImage supplies differences inside the moving preimage;
its exact kernel and a good conjugate lift the result to all of W. -/
theorem localZSpan_le_goodConjugateSpan_sup_radius
    (source : LocalSource L R) (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    (hn : ¬ ⁅Z R a, Q R c⁆ ≤ fixedCore R c)
    (f : FrameAt a c) (hop : ¬ f.SameOrientation) (s : EdgeData a c)
    (hcu : Adjacent R c u) :
    localZSpan R a c ≤ goodConjugateSpan a c s.neighbor u ⊔ V R u := by
  have hb₂ : 2 < geometry.b R := by omega
  have hbad := bad_coordinate_image_sup_radius_ne_top common hb ha hc hd hn f hop s hcu
  exact localZSpan_le_goodConjugateSpan_sup_radius_of_coordinates
    source hc hd hb₂ f hop s hcu hbad
    (good_moving_coordinate_image_eq_top source hc hd hb₂ f hop s hcu hbad)

/-- Discharge the local cover in the geometric path-selection consumer.
Escape of the specified local orbit remains the independent path premise;
no coordinate, generation or centralizer premise is added. -/
theorem pathPlacement_of_spanEscape_and_localSpans
    (source : LocalSource L R) (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    (hn : ¬ ⁅Z R a, Q R c⁆ ≤ fixedCore R c)
    (f : FrameAt a c) (hop : ¬ f.SameOrientation) (s : EdgeData a c)
    (escape : SpanEscape geometry a c) :
    Nonempty (PathPlacement geometry a c s.neighbor) := by
  apply pathPlacement_of_spanEscape_and_cover ha hc hb s.toMovingSeed escape
  intro u hcu
  exact localZSpan_le_goodConjugateSpan_sup_radius
    source common hb ha hc hd hn f hop s hcu

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection
