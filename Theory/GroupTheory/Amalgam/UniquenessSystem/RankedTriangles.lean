module
public import Theory.GroupTheory.Amalgam.UniquenessSystem.TriangleHomotopy

/-!
# Triangle contraction from a ranked edge reduction

Choose a rooted path to every vertex. Tree edges agree with these paths;
every other edge can be replaced across a triangle by two edges of smaller
rank. Induction therefore identifies every edge path with its rooted path,
and reverse-path cancellation contracts every loop. The depth-two tree
variant isolates the finite certificate used by the Hall–Janko graph.

Source: the elementary triangle moves and cycle-base method of Aschbacher,
*Sporadic Groups* (1994), §§34–35 and 37.
-/

public section
namespace SimpleGraph
open Walk Walk.TriangleHomotopy
variable {V : Type*} {Γ : SimpleGraph V}

/-- A rooted path system and a strictly decreasing triangle reduction for its edges. -/
structure RankedTriangleContraction (Γ : SimpleGraph V) where
  root : V
  path : (x : V) → Γ.Walk root x
  rank : V → V → ℕ
  initial : ∀ {x y} (h : Γ.Adj x y), rank x y = 0 →
    TriangleHomotopy ((path x).append h.toWalk) (path y)
  reduce : ∀ {x y}, Γ.Adj x y → rank x y ≠ 0 →
    ∃ z, Γ.Adj x z ∧ Γ.Adj z y ∧ rank x z < rank x y ∧ rank z y < rank x y

namespace RankedTriangleContraction
variable (D : RankedTriangleContraction Γ)

theorem edge {x y : V} (h : Γ.Adj x y) :
    TriangleHomotopy ((D.path x).append h.toWalk) (D.path y) := by
  have go : ∀ n x y (h : Γ.Adj x y), D.rank x y = n →
      TriangleHomotopy ((D.path x).append h.toWalk) (D.path y) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x y h hn
      by_cases hz : D.rank x y = 0
      · exact D.initial h hz
      obtain ⟨z, hxz, hzy, hl, hr⟩ := D.reduce h hz
      have h₁ := (ih (D.rank x z) (hn ▸ hl) x z hxz rfl).append_right hzy.toWalk
      have h₂ := ih (D.rank z y) (hn ▸ hr) z y hzy rfl
      have h₃ := (TriangleHomotopy.triangle hxz hzy h .nil).append_left (D.path x)
      apply h₃.symm.trans
      simpa only [← Walk.append_assoc, Walk.cons_append, Walk.nil_append] using h₁.trans h₂
  exact go _ x y h rfl

theorem walk {x y : V} (p : Γ.Walk x y) :
    TriangleHomotopy ((D.path x).append p) (D.path y) := by
  induction p with
  | nil => simpa only [Walk.append_nil] using TriangleHomotopy.refl (D.path _)
  | cons h p ih =>
    have he := (D.edge h).append_right p
    simpa only [← Walk.append_assoc, Walk.cons_append, Walk.nil_append] using he.trans ih

include D in
theorem simplyConnected : Γ.TriangleSimplyConnected := by
  intro x p
  have h := (D.walk p).append_left (D.path x).reverse
  have hb : TriangleHomotopy ((D.path x).reverse.append (D.path x)) .nil := by
    simpa only [Walk.reverse_reverse] using TriangleHomotopy.append_reverse (D.path x).reverse
  have hc := hb.append_right p
  simp only [Walk.nil_append, ← Walk.append_assoc] at hc
  exact hc.symm.trans (h.trans hb)
end RankedTriangleContraction
/-- Graph isomorphisms preserve triangle simple connectivity. -/
theorem TriangleSimplyConnected.of_iso {W : Type*} {Δ : SimpleGraph W}
    (e : Γ ≃g Δ) (h : Γ.TriangleSimplyConnected) : Δ.TriangleSimplyConnected := by
  have hp : ∀ x (p : Δ.Walk x x),
      TriangleHomotopy (p.map (e.toHom.comp e.symm.toHom)) .nil := by
    intro x p
    have hh := (h (e.symm x) (p.map e.symm.toHom)).map e.toHom
    rw [Walk.map_map] at hh
    exact hh
  have he : e.toHom.comp e.symm.toHom = Hom.id := by
    ext a
    exact e.apply_symm_apply a
  rw [he] at hp
  intro x p
  have hh := hp x p
  rw [Walk.map_id] at hh
  exact hh

namespace TwoStepTree
variable [DecidableEq V] (root : V) (parent : V → V)
    (hroot : parent root = root)
    (htree : ∀ i, parent (parent i) = root ∧
      (i ≠ root → Γ.Adj (parent i) i) ∧
      (parent i ≠ root → Γ.Adj root (parent i)))

private def path (i : V) : Γ.Walk root i := by
  by_cases hi : i = root
  · subst i
    exact .nil
  · by_cases hp : parent i = root
    · exact (hp ▸ (htree i).2.1 hi).toWalk
    · exact .cons ((htree i).2.2 hp) ((htree i).2.1 hi).toWalk

private theorem path_parent (i : V) (hi : i ≠ root) :
    (path root parent htree (parent i)).append ((htree i).2.1 hi).toWalk =
      path root parent htree i := by
  have hpp := (htree i).1
  by_cases hp : parent i = root
  · cases hp
    simp [path, hi]
  · simp [path, hi, hp, hpp]

include hroot htree in
/-- Triangle reduction from a rooted tree of depth at most two. Numerical ranks
strictly decrease along the two replacement edges. -/
theorem simplyConnected (rank : V → V → ℕ)
    (hinitial : ∀ i j, Γ.Adj i j → rank i j = 0 → parent i = j ∨ parent j = i)
    (hreduce : ∀ i j, Γ.Adj i j → rank i j ≠ 0 →
      ∃ k, Γ.Adj i k ∧ Γ.Adj k j ∧ rank i k < rank i j ∧ rank k j < rank i j) :
    Γ.TriangleSimplyConnected := by
  let D : RankedTriangleContraction Γ := {
    root := root
    path := path root parent htree
    rank := rank
    initial := by
      intro i j hij hr
      obtain h | h := hinitial i j hij hr
      · have hi : i ≠ root := by
          intro he
          subst i
          have hj : j = root := by simpa only [hroot] using h.symm
          rw [hj] at hij
          exact Γ.irrefl hij
        have hp := path_parent root parent htree i hi
        have he : path root parent htree i =
            (path root parent htree j).append hij.symm.toWalk := by
          rw [← hp]
          subst j
          rfl
        rw [he]
        simpa only [← Walk.append_assoc, Walk.cons_append, Walk.nil_append, Walk.append_nil] using
          (TriangleHomotopy.backtrack hij.symm .nil).append_left (path root parent htree j)
      · have hj : j ≠ root := by
          intro he
          subst j
          have hi : i = root := by simpa only [hroot] using h.symm
          rw [hi] at hij
          exact Γ.irrefl hij
        have hp := path_parent root parent htree j hj
        subst i
        rw [hp]
        exact .refl _
    reduce := fun h hr => hreduce _ _ h hr }
  exact D.simplyConnected
end TwoStepTree
end SimpleGraph
