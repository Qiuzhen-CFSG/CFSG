module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.Spans
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Paths

/-!
# Replacing the critical midpoint by a noncommuting orbit generator

If Z_rho does not commute with an orbit span at distance two from alpha,
select an M-colored Z-layer in V_alpha which does not centralize Z_rho.
Minimal critical distance makes their distance four. Reversal and the
published escape fact force V_rho out of Q_alpha. A second critical shift
then constructs a critical segment based at alpha with midpoint rho.

This proves the critical-path part of the reapplication in original MS93
(1993), (4.6.12), p.912. It does not establish the large-intersection condition
for the replacement segment or recognize its quotient module.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch
variable {M : Type*} [Group M] {R : Subgroup M}

theorem color_of_distance_two (c : Vertex R)
    (hc : (cosetGraph R).dist (alpha R) c = 2) : color R c = false := by
  obtain ⟨p, hp⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist (alpha R) c
  have h : Even p.length := by rw [hp, hc]; decide
  exact ((walk_even_iff_color_eq R p).mp h).symm

variable {L : Subgroup M} (source : LocalSource L R) {geometry : Geometry R}
  (common : CommonFacts R source geometry)
include common

theorem criticalSegment_through_of_escape (hb : geometry.b R = 4)
    (c : Vertex R) (hc : (cosetGraph R).dist (alpha R) c = 2)
    (hescape : ¬ V R c ≤ Q R (alpha R)) : ∃ s : CriticalSegment geometry, s.middle = c := by
  have hcol := color_of_distance_two c hc
  have hd : (cosetGraph R).dist c (alpha R) + 2 = geometry.b R := by
    rw [(cosetGraph R).dist_comm (u := c) (v := alpha R), hc, hb]
  obtain ⟨t, htc, htd, hcrit⟩ :=
    DistanceEight.PathCentrality.exists_critical_shift R hcol hd hescape
  exact ⟨⟨t, c, common.critical_reverse t htc (alpha R) rfl hcrit,
    hc, ((cosetGraph R).dist_comm (u := c) (v := t)).trans htd⟩, rfl⟩

/-- A noncommuting orbit span supplies a critical path with the selected
vertex as midpoint. Only the published critical reversal and escape facts
are used; the small-intersection condition remains a separate issue. -/
theorem criticalSegment_through_of_noncommuting (hb : geometry.b R = 4)
    (c rho : Vertex R)
    (hc : (cosetGraph R).dist c (alpha R) = 2)
    (hrho : (cosetGraph R).dist (alpha R) rho = 2)
    (hne : ⁅Z R rho, orbitSpan c⁆ ≠ ⊥) : ∃ s : CriticalSegment geometry, s.middle = rho := by
  have hrcol := color_of_distance_two rho hrho
  have hV : ¬ V R (alpha R) ≤ centralizer (Z R rho : Set (FreeAmalgam R)) := by
    intro h
    apply hne
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr ((orbitSpan_le_radius c hc.le).trans h)
  obtain ⟨t, htcol, htd, ht⟩ : ∃ t, color R t = false ∧
      (cosetGraph R).dist t (alpha R) ≤ 2 ∧
      ¬ Z R t ≤ centralizer (Z R rho : Set (FreeAmalgam R)) := by
    simpa only [DistanceEight.PathCentrality.V_le_iff R (a := alpha R) rfl, not_forall, exists_prop] using hV
  have hnQ : ¬ Z R t ≤ Q R rho := by
    intro h
    apply ht
    exact h.trans (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes rho hrcol)))
  have hmin := criticalDistance_le R t (geometry.exists_critical t htcol) hnQ
  rw [geometry.distance_constant t htcol] at hmin
  change geometry.b R ≤ _ at hmin
  have htri := (cosetGraph_connected R).dist_triangle (u := t) (v := alpha R) (w := rho)
  have htd2 : (cosetGraph R).dist t (alpha R) = 2 := by rw [hb] at hmin; omega
  have ht4 : (cosetGraph R).dist t rho = 4 := by rw [hb] at hmin; omega
  have hcrit : CriticalPair R t rho (geometry.exists_critical t htcol) := by
    refine ⟨?_, hnQ⟩
    rw [geometry.distance_constant t htcol]
    exact ht4.trans hb.symm
  have hrev := common.critical_reverse t htcol rho hrcol hcrit
  have hescape : ¬ V R rho ≤ Q R (alpha R) := by
    apply common.escape rho hrcol t hrev (alpha R)
    · exact ((cosetGraph R).dist_comm (u := alpha R) (v := t)).trans htd2
    · rw [(cosetGraph R).dist_comm (u := rho) (v := alpha R), hrho,
        (cosetGraph R).dist_comm (u := rho) (v := t), ht4]
  exact criticalSegment_through_of_escape source common hb rho hrho hescape

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch
