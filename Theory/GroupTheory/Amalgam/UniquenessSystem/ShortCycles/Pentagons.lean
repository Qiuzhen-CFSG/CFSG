module
public import Theory.GroupTheory.Amalgam.UniquenessSystem.ShortCycles

/-!
# Pentagon moves after square contraction

Connected nonedge common-neighbor graphs identify two-step paths. This
contracts a pentagon when its first, third and fourth vertices have a common
neighbor. Separately, a repeated vertex or a chord from the first vertex to
the third or fourth reduces the loop to triangles and squares. These lemmas
leave only the opposite-edge configurations used in source J₂ recognition;
they do not postulate a common neighbor for every edge and distant vertex.

Source: Aschbacher, *Sporadic Groups* (1994), 34.6 and 34.8, applied in
47.9, pp.265–266.
-/

public section
namespace SimpleGraph
open Walk Walk.TriangleHomotopy
variable {V : Type*} {Γ : SimpleGraph V}

private theorem paths_of_append_reverse {x y : V} (p q : Γ.Walk x y)
    (h : (p.append q.reverse).TriangleHomotopy .nil) : p.TriangleHomotopy q := by
  have hq : (q.reverse.append q).TriangleHomotopy .nil := by
    simpa only [Walk.reverse_reverse] using TriangleHomotopy.append_reverse q.reverse
  have h₁ := hq.append_left p
  have h₂ := h.append_right q
  simp only [Walk.append_nil] at h₁
  simp only [Walk.nil_append, ← Walk.append_assoc] at h₂
  exact h₁.symm.trans h₂

/-- Connected nonedge common-neighbor graphs identify any two two-step paths.
This requires no common neighbor for triples. -/
theorem twoStep_triangleHomotopy
    (hconn : ∀ x y : V, x ≠ y → ¬ Γ.Adj x y →
      (Γ.commonNeighborGraph x y).Preconnected)
    {x y a b : V} (hxa : Γ.Adj x a) (hay : Γ.Adj a y)
    (hxb : Γ.Adj x b) (hby : Γ.Adj b y) :
    TriangleHomotopy (.cons hxa hay.toWalk) (.cons hxb hby.toWalk) := by
  apply paths_of_append_reverse
  apply square_triangleHomotopy hconn
  simp

/-- A common neighbor of the first, third and fourth vertices contracts a
pentagon once all squares contract (Aschbacher, 34.8). -/
theorem pentagon_triangleHomotopy_of_common
    (hconn : ∀ x y : V, x ≠ y → ¬ Γ.Adj x y →
      (Γ.commonNeighborGraph x y).Preconnected)
    {a b c d e v : V} (hab : Γ.Adj a b) (hbc : Γ.Adj b c)
    (hcd : Γ.Adj c d) (hde : Γ.Adj d e) (hea : Γ.Adj e a)
    (hav : Γ.Adj a v) (hcv : Γ.Adj c v) (hdv : Γ.Adj d v) :
    TriangleHomotopy (.cons hab (.cons hbc (.cons hcd (.cons hde hea.toWalk)))) .nil := by
  have h := (twoStep_triangleHomotopy hconn hab hbc hav hcv.symm).append_right
    (.cons hcd (.cons hde hea.toWalk))
  exact h.trans ((TriangleHomotopy.cons hav
    (.triangle hcv.symm hcd hdv.symm (.cons hde hea.toWalk))).trans
      (square_triangleHomotopy hconn a (.cons hav (.cons hdv.symm (.cons hde hea.toWalk)))
        (by simp)))

/-- To contract a five-step loop it suffices to handle the case where its
first vertex is distinct from, and nonadjacent to, its third and fourth.
All other cases contract by a chord or a backtrack and the square criterion. -/
theorem pentagon_triangleHomotopy_of_nonadjacent
    (hconn : ∀ x y : V, x ≠ y → ¬ Γ.Adj x y →
      (Γ.commonNeighborGraph x y).Preconnected)
    {a b c d e : V} (hab : Γ.Adj a b) (hbc : Γ.Adj b c)
    (hcd : Γ.Adj c d) (hde : Γ.Adj d e) (hea : Γ.Adj e a)
    (hfar : a ≠ c → a ≠ d → ¬ Γ.Adj a c → ¬ Γ.Adj a d →
      TriangleHomotopy (.cons hab (.cons hbc (.cons hcd (.cons hde hea.toWalk)))) .nil) :
    TriangleHomotopy (.cons hab (.cons hbc (.cons hcd (.cons hde hea.toWalk)))) .nil := by
  by_cases hac : a = c
  · subst c
    exact (TriangleHomotopy.backtrack hab (.cons hcd (.cons hde hea.toWalk))).trans
      ((TriangleHomotopy.triangle hcd hde hea.symm hea.toWalk).trans (.backtrack hea.symm .nil))
  by_cases had : a = d
  · subst d
    exact (TriangleHomotopy.triangle hab hbc hcd.symm (.cons hcd (.cons hde hea.toWalk))).trans
      ((TriangleHomotopy.backtrack hcd.symm (.cons hde hea.toWalk)).trans (.backtrack hde .nil))
  by_cases hc : Γ.Adj a c
  · exact (TriangleHomotopy.triangle hab hbc hc (.cons hcd (.cons hde hea.toWalk))).trans
      (square_triangleHomotopy hconn a (.cons hc (.cons hcd (.cons hde hea.toWalk))) (by simp))
  by_cases hd : Γ.Adj a d
  · exact (TriangleHomotopy.cons hab (.cons hbc (.cons hcd
      (.triangle hde hea hd.symm .nil)))).trans
      (square_triangleHomotopy hconn a (.cons hab (.cons hbc (.cons hcd hd.symm.toWalk))) (by simp))
  exact hfar hac had hc hd

end SimpleGraph
