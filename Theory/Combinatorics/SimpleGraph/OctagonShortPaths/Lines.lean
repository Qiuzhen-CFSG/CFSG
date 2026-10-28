module

public import Theory.Combinatorics.SimpleGraph.OctagonShortPaths.OrderTwoFour

/-!
# Recovering the lines from the point graph

Every adjacent point pair has a unique common line. A triangle in the point
graph lies on that line: otherwise its three short incidence paths would give
a cycle of length at most six. Thus incidence on a line is recovered from any
two distinct points on it and their common point-graph neighbors.

Source: the line-reconstruction step in Aschbacher–Smith J.5.7, printed p.448.
-/

public section
namespace SimpleGraph.OctagonShortPaths.OrderTwoFourDatum
variable {V : Type*} [Fintype V] {G : SimpleGraph V} (D : OrderTwoFourDatum G)
include D

theorem exists_unique_line {u v : V} (hd : G.dist u v=2) :
    ∃!l,G.Adj u l ∧G.Adj v l := by
  obtain ⟨l,⟨hul,hl⟩,huniq⟩ := unique_predecessor D.connected D.cycle_bound v u (by omega) (by omega)
  have hlv : G.dist l v=1 := by omega
  refine ⟨l,⟨hul,(dist_eq_one_iff_adj.mp hlv).symm⟩,?_⟩
  rintro m ⟨hum,hvm⟩
  exact huniq m ⟨hum,by rw [dist_eq_one_iff_adj.mpr hvm.symm,hd]⟩

theorem point_triangle_collinear {u v w l : V}
    (hu : D.color u=0) (_hv : D.color v=0) (hw : D.color w=0)
    (huw : G.dist u w=2) (hvw : G.dist v w=2) (huv : u≠v)
    (hul : G.Adj u l) (hvl : G.Adj v l) : G.Adj w l := by
  by_contra hnot
  obtain ⟨m,⟨hum,hwm⟩,_⟩ := D.exists_unique_line huw
  obtain ⟨n,⟨hvn,hwn⟩,_⟩ := D.exists_unique_line hvw
  have hcolorl : D.color l=1 := by simpa [hu] using (D.color_adj hul).symm
  have hlw : l≠w := by intro he; rw [he,hw] at hcolorl; exact zero_ne_one hcolorl
  have hln : l≠n := by intro he; exact hnot (he ▸ hwn)
  have hlm : l≠m := by intro he; exact hnot (he ▸ hwm)
  have huw' : u≠w := by intro he; simp [he] at huw
  have hvw' : v≠w := by intro he; simp [he] at hvw
  let p : G.Walk l w := Walk.cons hul.symm (Walk.cons hum (Walk.cons hwm.symm Walk.nil))
  let q : G.Walk l w := Walk.cons hvl.symm (Walk.cons hvn (Walk.cons hwn.symm Walk.nil))
  have hp : p.IsPath := by
    simp [p,Walk.cons_isPath_iff,hwm.ne.symm,hum.ne,huw',hul.ne.symm,hlm,hlw]
  have hq : q.IsPath := by
    simp [q,Walk.cons_isPath_iff,hwn.ne.symm,hvn.ne,hvw',hvl.ne.symm,hln,hlw]
  have he := paths_eq D.cycle_bound hp hq (by decide : 3+3<16)
  have he' := congrArg (fun a : G.Walk l w=>a.getVert 1) he
  exact huv (by simpa [p,q] using he')

/-- Lines are recovered from point adjacency: the third point is precisely a
common point-graph neighbor of any two distinct points on the line. -/
theorem line_incidence_iff {u v l w : V}
    (hu : D.color u=0) (hv : D.color v=0) (hw : D.color w=0)
    (hul : G.Adj u l) (hvl : G.Adj v l) (huv : u≠v) :
    G.Adj w l ↔ w=u ∨ w=v ∨ (G.dist u w=2 ∧ G.dist v w=2) := by
  constructor
  · intro hwl
    by_cases hwu : w=u
    · exact Or.inl hwu
    by_cases hwv : w=v
    · exact Or.inr (Or.inl hwv)
    exact Or.inr (Or.inr ⟨distance_two_of_common D.connected D.cycle_bound (Ne.symm hwu) hul hwl.symm,
      distance_two_of_common D.connected D.cycle_bound (Ne.symm hwv) hvl hwl.symm⟩)
  · rintro (rfl | rfl | ⟨huw,hvw⟩)
    · exact hul
    · exact hvl
    · exact D.point_triangle_collinear hu hv hw huw hvw huv hul hvl

end SimpleGraph.OctagonShortPaths.OrderTwoFourDatum
