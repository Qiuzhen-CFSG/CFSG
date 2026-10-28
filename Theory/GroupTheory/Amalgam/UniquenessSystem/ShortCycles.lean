module
public import Theory.GroupTheory.Amalgam.UniquenessSystem.TriangleHomotopy

/-!
# Contracting squares and pentagons in a graph of diameter two

A walk can be shortened by replacing each prefix with a path of length
at most two. Each replacement bounds a loop of length at most five.
Contraction of these short loops therefore contracts every loop. Loops
of length at most three already cancel by triangles and backtracks;
connected common-neighbor graphs also contract the squares.

This gives the square-and-pentagon route of Aschbacher, *Sporadic Groups*
(1994), 34.5–34.6, used for J₂ in 47.7–47.9, pp.264–266. It does not
assume that each edge and a distant vertex have a common neighbor.
-/

public section
namespace SimpleGraph
open Walk Walk.TriangleHomotopy
variable {V : Type*} {Γ : SimpleGraph V}

private theorem homotopy_of_closed_append {x y : V} (p q : Γ.Walk x y)
    (h : (p.append q.reverse).TriangleHomotopy .nil) : p.TriangleHomotopy q := by
  have hq : (q.reverse.append q).TriangleHomotopy .nil := by
    simpa only [Walk.reverse_reverse] using TriangleHomotopy.append_reverse q.reverse
  have h₁ := hq.append_left p
  have h₂ := h.append_right q
  simp only [Walk.append_nil] at h₁
  simp only [Walk.nil_append, ← Walk.append_assoc] at h₂
  exact h₁.symm.trans h₂

/-- In a graph of diameter at most two, contraction of loops of length at
most five contracts all loops. No common neighbor for every triple is assumed. -/
theorem triangleSimplyConnected_of_short_loops
    (hshort : ∀ x y : V, ∃ p : Γ.Walk x y, p.length ≤ 2)
    (hsmall : ∀ (x : V) (p : Γ.Walk x x), p.length ≤ 5 → p.TriangleHomotopy .nil) :
    Γ.TriangleSimplyConnected := by
  have shorten (x : V) {a b : V} (p : Γ.Walk a b) :
      ∀ q : Γ.Walk x a, q.length ≤ 2 →
        ∃ r : Γ.Walk x b, r.length ≤ 2 ∧ (q.append p).TriangleHomotopy r := by
    induction p with
    | nil => intro q hq; exact ⟨q, hq, by simpa using TriangleHomotopy.refl q⟩
    | @cons a b c h p ih =>
      intro q hq
      obtain ⟨r, hr⟩ := hshort x b
      have hc : ((q.append h.toWalk).append r.reverse).TriangleHomotopy .nil := by
        apply hsmall
        simp only [Walk.length_append, Walk.length_reverse, Walk.length_cons,
          Walk.length_nil]
        omega
      have hs := homotopy_of_closed_append (q.append h.toWalk) r hc
      obtain ⟨s, hlen, hh⟩ := ih r hr
      refine ⟨s, hlen, ?_⟩
      have he := (hs.append_right p).trans hh
      change ((q.append (.cons h .nil)).append p).TriangleHomotopy s at he
      simpa only [← Walk.append_assoc, Walk.cons_append, Walk.nil_append] using he
  intro x p
  obtain ⟨q, hq, hp⟩ := shorten x p .nil (by simp)
  exact hp.trans (hsmall x q (by omega))

/-- The diameter-two criterion requires only squares and pentagons: shorter
closed walks cancel by a triangle move or a backtrack. -/
theorem triangleSimplyConnected_of_squares_pentagons
    (hshort : ∀ x y : V, ∃ p : Γ.Walk x y, p.length ≤ 2)
    (hsquare : ∀ (x : V) (p : Γ.Walk x x), p.length = 4 → p.TriangleHomotopy .nil)
    (hpentagon : ∀ (x : V) (p : Γ.Walk x x), p.length = 5 → p.TriangleHomotopy .nil) :
    Γ.TriangleSimplyConnected := by
  apply triangleSimplyConnected_of_short_loops hshort
  intro x p hp
  by_cases h4 : p.length = 4
  · exact hsquare x p h4
  by_cases h5 : p.length = 5
  · exact hpentagon x p h5
  have hp3 : p.length ≤ 3 := by omega
  cases p with
  | nil => exact .refl _
  | @cons x a x h p =>
    cases p with
    | nil => exact (Γ.irrefl h).elim
    | @cons a b x h' p =>
      cases p with
      | nil => exact .backtrack h .nil
      | @cons b c x h'' p =>
        cases p with
        | nil =>
          exact (TriangleHomotopy.triangle h h' h''.symm h''.toWalk).trans
            (.backtrack h''.symm .nil)
        | cons h''' p => simp at hp3

private theorem two_step_of_common_path {x y : V}
    {a b : {z : V // Γ.Adj x z ∧ Γ.Adj y z}}
    (p : (Γ.commonNeighborGraph x y).Walk a b) :
    TriangleHomotopy (.cons a.property.1 a.property.2.symm.toWalk)
      (.cons b.property.1 b.property.2.symm.toWalk) := by
  induction p with
  | nil => exact .refl _
  | @cons a c b hac p ih =>
    have hac' : Γ.Adj a.val c.val := hac
    exact ((TriangleHomotopy.triangle a.property.1 hac' c.property.1 c.property.2.symm.toWalk).symm.trans
      (.cons a.property.1 (.triangle hac' c.property.2.symm a.property.2.symm .nil))).symm.trans ih

/-- Connected common-neighbor graphs contract every square. -/
theorem square_triangleHomotopy
    (hconn : ∀ x y : V, x ≠ y → ¬ Γ.Adj x y →
      (Γ.commonNeighborGraph x y).Preconnected)
    (x : V) (p : Γ.Walk x x) (hlen : p.length = 4) :
    p.TriangleHomotopy .nil := by
  cases p with
  | nil => simp at hlen
  | @cons x a x h p =>
    cases p with
    | nil => simp at hlen
    | @cons a b x h' p =>
      cases p with
      | nil => simp at hlen
      | @cons b c x h'' p =>
        cases p with
        | nil => simp at hlen
        | @cons c d x h''' p =>
          cases p with
          | cons h4 p => simp at hlen
          | nil =>
            have hh : TriangleHomotopy (.cons h h'.toWalk)
                (.cons h'''.symm h''.symm.toWalk) := by
              by_cases he : x = b
              · subst b
                exact (TriangleHomotopy.backtrack h .nil).trans
                  (TriangleHomotopy.backtrack h'''.symm .nil).symm
              by_cases ha : Γ.Adj x b
              · exact (TriangleHomotopy.triangle h h' ha .nil).trans
                  (TriangleHomotopy.triangle h'''.symm h''.symm ha .nil).symm
              obtain ⟨q⟩ := hconn x b he ha ⟨a, h, h'.symm⟩ ⟨c, h'''.symm, h''⟩
              exact two_step_of_common_path q
            have ht := hh.append_right (.cons h'' h'''.toWalk)
            exact ht.trans ((TriangleHomotopy.cons h'''.symm
              (.backtrack h''.symm h'''.toWalk)).trans (.backtrack h'''.symm .nil))

/-- A diameter-two graph with connected nonedge common-neighbor graphs needs
only pentagon contraction for triangle simple connectivity. -/
theorem triangleSimplyConnected_of_common_connected_pentagons
    (hshort : ∀ x y : V, ∃ p : Γ.Walk x y, p.length ≤ 2)
    (hconn : ∀ x y : V, x ≠ y → ¬ Γ.Adj x y →
      (Γ.commonNeighborGraph x y).Preconnected)
    (hpentagon : ∀ (x : V) (p : Γ.Walk x x), p.length = 5 → p.TriangleHomotopy .nil) :
    Γ.TriangleSimplyConnected :=
  triangleSimplyConnected_of_squares_pentagons hshort (square_triangleHomotopy hconn) hpentagon

end SimpleGraph
