module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.RadiusTwoControl

/-!
# Selecting the terminal radius actor on a critical path

A radius-two escape forces a neighboring radius-one escape. A geodesic
through the chosen terminal edge supplies the first neighbor, the third-last
vertex and all required distance budgets; the first neighbor's radius span
lies in the terminal core and hence cannot be the escaping neighbor.
No tree hypothesis or separately assumed path configuration is used.

Source: DGS, *Groups and Graphs* (1985), (7.5), printed pp.130--131.
-/

public noncomputable section
open Subgroup
open Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

theorem graph_radius_two_escape_neighbor (h : LocallyRankOneTriple P B)
    {v u t : Vertex (family P)} (hvu : (graph (family P)).Adj v u)
    (hesc : ¬ V (family P) v 2 ≤ Q (family P) t)
    (hu : V (family P) u 1 ≤ Q (family P) t) :
    ∃ a, (graph (family P)).Adj v a ∧ u ≠ a ∧ ¬ V (family P) a 1 ≤ Q (family P) t := by
  classical
  by_contra hn
  push Not at hn
  have hall (a : Vertex (family P)) (ha : (graph (family P)).Adj v a) :
      V (family P) a 1 ≤ Q (family P) t := by
    by_cases he : u = a
    · exact he ▸ hu
    · exact hn a ha he
  apply hesc
  apply iSup_le
  intro z
  apply iSup_le
  intro hz
  by_cases he : z = v
  · subst z
    have hzv : Z (family P) v ≤ V (family P) u 1 :=
      le_iSup_of_le v (le_iSup_of_le ((mem_ball_one _ _ _).mpr (Or.inl hvu.symm)) le_rfl)
    exact hzv.trans hu
  · obtain ⟨a,ha,hda⟩ := exists_predecessor (family P) h.generate z v he
    have hdz := (mem_ball_iff (family P) h.generate v z 2).mp hz
    have hza : z ∈ ball (family P) a 1 := by
      apply (mem_ball_iff (family P) h.generate _ _ _).mpr
      rw [SimpleGraph.dist_comm] at hdz ⊢
      omega
    have hza' : Z (family P) z ≤ V (family P) a 1 :=
      le_iSup_of_le z (le_iSup_of_le hza le_rfl)
    exact hza'.trans (hall a ha)

theorem graph_terminal_actor_configuration (h : LocallyRankOneTriple P B)
    (hS : ∀ z, Stellmacher.IsSylowSubgroupIn (Q (family P) z) (U (family P) z))
    {v w t y : Vertex (family P)}
    (hc : IsCriticalPair (family P) v w) (hb : 6 ≤ b (family P))
    (hwt : (graph (family P)).Adj w t) (hty : (graph (family P)).Adj t y)
    (hdy : (graph (family P)).dist v y + 2 = b (family P))
    (hesc : ¬ V (family P) v 2 ≤ Q (family P) t) :
    ∃ u a x : Vertex (family P),
      (graph (family P)).Adj v u ∧ (graph (family P)).Adj v a ∧ u ≠ a ∧
      (graph (family P)).Adj y x ∧
      (graph (family P)).dist u w + 1 = b (family P) ∧
      (graph (family P)).dist v x + 3 = b (family P) ∧
      ¬ V (family P) a 1 ≤ Q (family P) t := by
  have hvy : v ≠ y := by
    intro he
    rw [he,SimpleGraph.dist_self] at hdy
    omega
  obtain ⟨x,hyx,hdx⟩ := exists_predecessor (family P) h.generate v y hvy
  have hxv : x ≠ v := by
    intro he
    rw [he,SimpleGraph.dist_self] at hdx
    omega
  obtain ⟨u,hvu,hdu⟩ := exists_predecessor (family P) h.generate x v hxv
  have hvud : (graph (family P)).dist v u = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hvu
  have hxyd : (graph (family P)).dist x y = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hyx.symm
  have hytd : (graph (family P)).dist y t = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hty.symm
  have htwd : (graph (family P)).dist t w = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hwt.symm
  have hux : (graph (family P)).dist u x + 1 = (graph (family P)).dist v x := by
    simpa only [SimpleGraph.dist_comm] using hdu
  have hut : (graph (family P)).dist u t + 2 ≤ b (family P) := by
    have h₁ := (connected_graph h).dist_triangle (u := u) (v := x) (w := y)
    have h₂ := (connected_graph h).dist_triangle (u := u) (v := y) (w := t)
    omega
  have huw : (graph (family P)).dist u w + 1 = b (family P) := by
    have h₁ := (connected_graph h).dist_triangle (u := u) (v := t) (w := w)
    have h₂ := (connected_graph h).dist_triangle (u := v) (v := u) (w := w)
    have hh := hc.1
    omega
  have hu : V (family P) u 1 ≤ Q (family P) t := graph_V_le_Q_of_distance h hS (by omega)
  obtain ⟨a,hva,hua,ha⟩ := graph_radius_two_escape_neighbor h hvu hesc hu
  exact ⟨u,a,x,hvu,hva,hua,hyx,huw,by omega,ha⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
