module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.First.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.First.Intersections
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.First.Calculations
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.First.Layer.WindowSelection

/-!
# Applying the second-layer calculation on the source path

Strict images at the three forward and three reversed centers fill the
literal edge quotients. One forward product then puts an edge displacement
of order four in H at its midpoint. Conjugacy transports the lower bound
to every M-vertex using `Escape.Initial.H_card_eq_base`.

The regular-window calculation proves the displacement lower bound using two
actual separated source choices. Evaluation of the edge action supplies the
strict image bounds on the same marked window, in both orientations. The final
producer discharges every extra premise of the older conditional assembly.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.1)(iv)--(v), p.896.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.First.Layer
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

variable {a : Vertex R}

/-- One forward product supplies the lower bound at every M-vertex by actual conjugacy. -/
theorem H_card_lower_of_forward_product (source : LocalSource L R)
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    (p : SourcePath R a)
    (hprod : (hatW R (p.walk.getVert 4) (p.walk.getVert 6) (p.walk.getVert 8) :
      Set (FreeAmalgam R)) * (Q R (p.walk.getVert 8) : Set (FreeAmalgam R)) =
        (Q R (p.walk.getVert 7) : Set (FreeAmalgam R))) :
    ∀ v, color R v = false → 4 ≤ Nat.card (H R v) := by
  have hc := p.even_color (i := 6) (by decide) (by decide)
  have hh : 4 ≤ Nat.card (H R (p.walk.getVert 6)) :=
    four_le_H_of_product source common earlier hc
      (p.even_color (i := 8) (by decide) (by decide))
      (adjacent_symm R (p.adjacent (i := 5) (by decide)))
      (adjacent_symm R (p.adjacent (i := 7) (by decide)))
      (by rw [SimpleGraph.dist_comm, p.distance (geometry := geometry) (i := 4) (j := 6) (by decide) (by decide)])
      (by rw [SimpleGraph.dist_comm, p.distance (geometry := geometry) (i := 6) (j := 8) (by decide) (by decide)])
      (p.distance (geometry := geometry) (i := 4) (j := 5) (by decide) (by decide)) hprod
  intro v hv
  rwa [Escape.Initial.H_card_eq_base _ hc, ← Escape.Initial.H_card_eq_base v hv] at hh

/-- Conditional final assembly from the six strict image bounds. The bounds
are supplied by the marked-window calculation in the unconditional producer below. -/
theorem layerFactsOnPath_of_large_images (source : LocalSource L R)
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    (p : SourcePath R a)
    (forward_image : ∀ i : ℕ, Even i → 2 ≤ i → i ≤ 6 →
      2 < (Q R (p.walk.getVert (i + 4))).relIndex
        (hatW R (p.walk.getVert i) (p.walk.getVert (i + 2)) (p.walk.getVert (i + 4))))
    (backward_image : ∀ i : ℕ, Even i → 8 ≤ i → i ≤ 12 →
      2 < (Q R (p.walk.getVert (i - 4))).relIndex
        (hatW R (p.walk.getVert i) (p.walk.getVert (i - 2)) (p.walk.getVert (i - 4)))) :
    LayerFactsOnPath R p := by
  have hf : ∀ i : ℕ, Even i → 2 ≤ i → i ≤ 6 →
      (hatW R (p.walk.getVert i) (p.walk.getVert (i + 2)) (p.walk.getVert (i + 4)) :
        Set (FreeAmalgam R)) * (Q R (p.walk.getVert (i + 4)) : Set (FreeAmalgam R)) =
          (Q R (p.walk.getVert (i + 3)) : Set (FreeAmalgam R)) := by
    intro i hi hi2 hi6
    apply hatW_product_of_large_image earlier (p.even_color hi (by omega))
      (p.even_color (hi.add (by decide : Even 4)) (by omega))
    · exact adjacent_symm R (by simpa only [Nat.add_assoc] using p.adjacent (i := i + 3) (by omega))
    · rw [SimpleGraph.dist_comm, p.distance (geometry := geometry) (by omega) (by omega)]; omega
    · rw [SimpleGraph.dist_comm, p.distance (geometry := geometry) (by omega) (by omega)]; omega
    · rw [p.distance (geometry := geometry) (by omega) (by omega)]; omega
    · exact forward_image i hi hi2 hi6
  refine ⟨hf, ?_, H_card_lower_of_forward_product source common earlier p (hf 4 (by decide) (by decide) (by decide))⟩
  intro i hi hi8 hi12
  have he : Even (i - 4) := by rw [Nat.even_iff] at hi ⊢; omega
  apply hatW_product_of_large_image earlier (p.even_color hi (by omega))
    (p.even_color he (by omega))
  · simpa only [show i - 4 + 1 = i - 3 by omega] using p.adjacent (i := i - 4) (by omega)
  · rw [p.distance (geometry := geometry) (by omega) (by omega)]; omega
  · rw [p.distance (geometry := geometry) (by omega) (by omega)]; omega
  · rw [SimpleGraph.dist_comm, p.distance (geometry := geometry) (by omega) (by omega)]; omega
  · exact backward_image i hi hi8 hi12


open PathCentrality PathCentrality.RegularPaths

private noncomputable def sourceWindow (earlier : Earlier R geometry)
    (p : SourcePath R a) (i : ℕ) (hi : Even i) (hi6 : i ≤ 6) :
    CriticalPath R geometry (p.walk.getVert i) (p.walk.getVert (i + 8)) := by
  have hlen : 8 ≤ (p.walk.drop i).length := by
    rw [SimpleGraph.Walk.drop_length, p.length_eq]
    omega
  have htarget : (p.walk.drop i).getVert 8 = p.walk.getVert (i + 8) :=
    SimpleGraph.Walk.drop_getVert _ _ _
  let w := ((p.walk.drop i).take 8).copy rfl htarget
  have hw : w.length = 8 := by
    rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.take_length, inf_eq_left.mpr hlen]
  exact ⟨p.even_color hi (by omega), w,
    hw.trans (p.critical i hi hi6).1.symm, p.critical_pair earlier hi hi6⟩

omit [Finite M] in
private theorem sourceWindow_getVert (earlier : Earlier R geometry)
    (p : SourcePath R a) (i : ℕ) (hi : Even i) (hi6 : i ≤ 6)
    (j : ℕ) (hj : j ≤ 8) :
    (sourceWindow earlier p i hi hi6).walk.getVert j = p.walk.getVert (i + j) := by
  simp only [sourceWindow, SimpleGraph.Walk.getVert_copy, SimpleGraph.Walk.take_getVert,
    inf_eq_right.mpr hj, SimpleGraph.Walk.drop_getVert]

omit [Finite M] in
private theorem sourceWindow_regular (earlier : Earlier R geometry)
    (p : SourcePath R a) (i : ℕ) (hi : Even i) (hi6 : i ≤ 6) :
    HasTurnConjugators R (sourceWindow earlier p i hi hi6) := by
  intro j hj hj2 hjend
  have hlen : (sourceWindow earlier p i hi hi6).walk.length = 8 :=
    (sourceWindow earlier p i hi hi6).length_eq_b.trans earlier.distance
  obtain ⟨g, hg, ht⟩ := p.turns (i + j) (hi.add hj) (by omega) (by omega)
  refine ⟨g, ?_, ?_⟩
  · rwa [sourceWindow_getVert earlier p i hi hi6 j (by omega)]
  · rw [sourceWindow_getVert earlier p i hi hi6 (j + 2) (by omega),
      sourceWindow_getVert earlier p i hi hi6 (j - 2) (by omega)]
    simpa only [Nat.add_assoc, show i + (j - 2) = i + j - 2 by omega] using ht

/-- All six literal setwise products and the H lower bound of MS93
(4.5.1)(iv--v), on the supplied source path and from the preceding outputs.
Each selected calculation uses precisely its translated or reversed window. -/
theorem layerFactsOnPath (source : LocalSource L R)
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    (p : SourcePath R a) : LayerFactsOnPath R p := by
  refine ⟨?_, ?_, H_card_lower common earlier⟩
  · intro i hi _ hi6
    have h := window_hatW_product common earlier (sourceWindow earlier p i hi hi6)
      (sourceWindow_regular earlier p i hi hi6)
    simpa only [sourceWindow_getVert earlier p i hi hi6 2 (by decide),
      sourceWindow_getVert earlier p i hi hi6 3 (by decide),
      sourceWindow_getVert earlier p i hi hi6 4 (by decide)] using h
  · intro i hi hi8 hi12
    have he : Even (i - 8) := by rw [Nat.even_iff] at hi ⊢; omega
    have he6 : i - 8 ≤ 6 := by omega
    let w := sourceWindow earlier p (i - 8) he he6
    have hr : HasTurnConjugators R (w.reverse common) :=
      (sourceWindow_regular earlier p (i - 8) he he6).reverse R common
    have hv (j : ℕ) (hj : j ≤ 8) :
        (w.reverse common).walk.getVert j = p.walk.getVert (i - j) := by
      change w.walk.reverse.getVert j = _
      rw [SimpleGraph.Walk.getVert_reverse, w.length_eq_b, earlier.distance,
        sourceWindow_getVert earlier p (i - 8) he he6 (8 - j) (by omega)]
      congr 1
      omega
    have h := window_hatW_product common earlier (w.reverse common) hr
    simpa only [hv 2 (by decide), hv 3 (by decide), hv 4 (by decide),
      show i - 8 + 8 = i by omega] using h

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.First.Layer
