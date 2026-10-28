module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.Paths.LocalSpans.BadImage.Calculation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.Paths.LocalSpans.BadImage.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.Paths.LocalSpans.BadImage.Incident
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.Edges.Parabolic

/-!
# The bad-span estimate from incident natural geometry

The bad conjugates all annihilate any natural vector fixed by the incident
actor. A nonzero such vector which also annihilates the literal intersection
V_u ∩ W therefore proves the displayed nonspanning estimate, including its
ambient version via the exact coordinate-image join formula.

The actual order-four displacement and the incident witness are explicit
premises here. Their source deductions are still needed for the unconditional
estimate in MS93 (4.4.1)(1), printed p.891.

The last consumer discharges the nonzero fixed-point and order-four premises
using the actual incident two-group and the independent selected-parabolic
plane calculation. Only that selected parabolic and a literal intersection
commutator bound remain as its inputs.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.LocalSpans
open BadImage
open Escape.PairingControl.Geometry.Selection.Centralizer.Generation.SourceDisplay
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R} {a c u : Vertex R}

/-- Sufficient marked geometry for the source's bad-image bound, retaining
the literal incident-radius intersection with W. -/
theorem bad_coordinate_image_sup_radius_ne_top_of_incident_point
    (common : CommonFacts R source geometry)
    (hc : color R c = false) (hd : (cosetGraph R).dist a c = 2)
    (hb : 2 < geometry.b R) (f : FrameAt a c) (hop : ¬ f.SameOrientation)
    (s : EdgeData a c) (hfour : Nat.card (edgeCommutator R a s.neighbor) = 4)
    (hcu : Adjacent R c u) (w : U R c) (hne : w ≠ 1)
    (hfixed : (w : FreeAmalgam R) ∈ centralizer (Q R u : Set (FreeAmalgam R)))
    (hradius : ∀ x : localZSpan R a c, (x : FreeAmalgam R) ∈ V R u →
      dotProduct (naturalCoordinates f w).toAdd
        (coordinates source hc hd hb f hop x).toAdd = 0) :
    coordinateImage source hc hd hb f hop (badConjugateSpan a c s.neighbor u) ⊔
      coordinateImage source hc hd hb f hop (V R u) ≠ ⊤ := by
  have hw : naturalCoordinates f w ≠ 1 := fun h => hne
    ((naturalCoordinates f).injective (h.trans (map_one _).symm))
  have hle : coordinateImage source hc hd hb f hop (badConjugateSpan a c s.neighbor u) ⊔
      coordinateImage source hc hd hb f hop (V R u) ≤
      Model.annihilator (naturalCoordinates f w) := by
    refine sup_le (bad_coordinate_image_le_annihilator common hc hd hb f hop s hfour hcu w hfixed) ?_
    rintro _ ⟨x, hx, rfl⟩
    exact hradius x hx
  intro he
  exact annihilator_ne_top _ hw (top_unique (he ▸ hle))

/-- Direct application to the literal ambient product in the source display. -/
theorem localZSpan_not_le_bad_sup_radius_of_incident_point
    (common : CommonFacts R source geometry)
    (hc : color R c = false) (hd : (cosetGraph R).dist a c = 2)
    (hb : 2 < geometry.b R) (f : FrameAt a c) (hop : ¬ f.SameOrientation)
    (s : EdgeData a c) (hfour : Nat.card (edgeCommutator R a s.neighbor) = 4)
    (hcu : Adjacent R c u) (w : U R c) (hne : w ≠ 1)
    (hfixed : (w : FreeAmalgam R) ∈ centralizer (Q R u : Set (FreeAmalgam R)))
    (hradius : ∀ x : localZSpan R a c, (x : FreeAmalgam R) ∈ V R u →
      dotProduct (naturalCoordinates f w).toAdd
        (coordinates source hc hd hb f hop x).toAdd = 0) :
    ¬ localZSpan R a c ≤ badConjugateSpan a c s.neighbor u ⊔ V R u := by
  apply not_le_of_coordinateImage_ne_top source hc hd hb f hop
  rw [coordinateImage_join_radius source hc hd hb f hop hcu _
    (badConjugateSpan_le a c s.neighbor u)]
  exact bad_coordinate_image_sup_radius_ne_top_of_incident_point
    common hc hd hb f hop s hfour hcu w hne hfixed hradius

/-- The opposite selected edge has the source's unconditional bad-image bound.

The selected parabolic supplies the order-four displacement for the supplied
edge, while the incident-radius pairing is obtained from the literal marked
intersection in `W`. -/
theorem bad_coordinate_image_sup_radius_ne_top
    (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    (hn : ¬ ⁅Z R a, Q R c⁆ ≤ fixedCore R c)
    (f : FrameAt a c) (hop : ¬ f.SameOrientation)
    (s : EdgeData a c) (hcu : Adjacent R c u) :
    coordinateImage source hc hd (show 2 < geometry.b R from by omega) f hop
        (badConjugateSpan a c s.neighbor u) ⊔
      coordinateImage source hc hd (show 2 < geometry.b R from by omega) f hop (V R u) ≠ ⊤ := by
  obtain ⟨p⟩ := parabolicSeed_nonempty common hb ha hc hd hn f hop
  obtain ⟨w, hne, hfixed, hradius⟩ :=
    exists_incident_radius_pairing common hc hd (by omega) f hop hcu
  exact bad_coordinate_image_sup_radius_ne_top_of_incident_point
    common hc hd (by omega) f hop s
    (edge_card_four_of_parabolic common hb ha hc hd f hop p s)
    hcu w hne hfixed hradius

/-- The unconditional bound gives noncontainment in the literal source span. -/
theorem localZSpan_not_le_bad_sup_radius
    (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    (hn : ¬ ⁅Z R a, Q R c⁆ ≤ fixedCore R c)
    (f : FrameAt a c) (hop : ¬ f.SameOrientation)
    (s : EdgeData a c) (hcu : Adjacent R c u) :
    ¬ localZSpan R a c ≤ badConjugateSpan a c s.neighbor u ⊔ V R u := by
  apply not_le_of_coordinateImage_ne_top source hc hd (by omega) f hop
  rw [coordinateImage_join_radius source hc hd (by omega) f hop hcu _
    (badConjugateSpan_le a c s.neighbor u)]
  exact bad_coordinate_image_sup_radius_ne_top common hb ha hc hd hn f hop s hcu

/-- Source assembly after incident-radius fixation. The independent
parabolic-selection theorem supplies p; fixation remains a geometric input. -/
theorem bad_coordinate_image_sup_radius_ne_top_of_radius_fixation
    (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (f : FrameAt a c) (hop : ¬ f.SameOrientation)
    (s : EdgeData a c) (p : ParabolicSeed geometry f) (hcu : Adjacent R c u)
    (hcomm : ⁅localZSpan R a c ⊓ V R u, Q R u⁆ ≤ B R c (geometry.Z_normal c)) :
    coordinateImage source hc hd (show 2 < geometry.b R from by omega) f hop
        (badConjugateSpan a c s.neighbor u) ⊔
      coordinateImage source hc hd (show 2 < geometry.b R from by omega) f hop (V R u) ≠ ⊤ := by
  obtain ⟨w, hne, he, hf⟩ := exists_incident_fixed_point common hc hcu
  exact bad_coordinate_image_sup_radius_ne_top_of_incident_point
    common hc hd (by omega) f hop s (edge_card_four_of_parabolic common hb ha hc hd f hop p s)
    hcu w hne hf (radius_annihilates_edge_of_commutator common hc hd (by omega) f hop hcu hcomm w he)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.LocalSpans
