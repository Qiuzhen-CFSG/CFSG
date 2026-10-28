module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Basic

/-!
# Predecessors on the actual critical geodesic

Uniqueness of paths in the amalgam tree identifies a vertex satisfying
Before with the indicated vertex on every shortest walk. Consecutive Before
vertices are adjacent. Consequently the contrary containment Vα ≤ Qα′−2
places R₀ inside the edge displacement at every specified predecessor of α′.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.1)(i), p.882.
These lemmas preserve the chosen critical pair and its specified path.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape
variable {M : Type*} [Group M] {R : Subgroup M} {geometry : Geometry R}

include geometry in

theorem Before.getVert {a a' c : Vertex R} {n : ℕ} (h : Before a a' c n)
    (w : (cosetGraph R).Walk a a') (hw : w.length = (cosetGraph R).dist a a') :
    w.getVert (w.length - n) = c := by
  obtain ⟨u, hu⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist a c
  obtain ⟨v, hv⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist c a'
  have hlength : (u.append v).length = (cosetGraph R).dist a a' := by
    rw [SimpleGraph.Walk.length_append, hu, hv, h.1]
    exact h.2
  have heq : w = u.append v := congrArg Subtype.val
    ((geometry.tree.isAcyclic.subsingleton_path a a').elim
      ⟨w, w.isPath_of_length_eq_dist hw⟩
      ⟨u.append v, (u.append v).isPath_of_length_eq_dist hlength⟩)
  have hindex : w.length - n = u.length := by have := h.2; omega
  rw [hindex, heq]
  simp [SimpleGraph.Walk.getVert_append]

include geometry in
theorem Before.adjacent {a a' c t : Vertex R} {n : ℕ}
    (hc : Before a a' c (n + 1)) (ht : Before a a' t n) : Adjacent R c t := by
  obtain ⟨w, hw⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist a a'
  have hn : n + 1 ≤ w.length := by have := hc.2; omega
  have hstep : w.length - (n + 1) + 1 = w.length - n := by omega
  have hadj := w.adj_getVert_succ (i := w.length - (n + 1)) (by omega)
  rw [hstep, hc.getVert (geometry := geometry) w hw, ht.getVert (geometry := geometry) w hw] at hadj
  exact (cosetGraph_adj R _ _).mp hadj

namespace Initial
variable [Finite M]

theorem radius_le_edge (p : Counterexample geometry) (t : Vertex R)
    (ht : Before p.a p.a' t 1) : radiusCommutator p.a p.a' ≤ edgeDisplacement p.a' t := by
  have hct : Adjacent R p.c t := p.before.adjacent (geometry := geometry) ht
  have hcol : color R t = true := by
    have hn := adjacent_color_ne R ht.endpoint_adjacent
    rw [p.end_color] at hn
    cases h : color R t <;> simp_all
  rw [radiusCommutator, commutator_comm]
  exact commutator_mono le_rfl (p.trapped.trans (Q_le_adjacent_h R hcol hct))

end Initial
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape
