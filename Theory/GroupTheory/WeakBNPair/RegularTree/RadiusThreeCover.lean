module
public import Theory.GroupTheory.WeakBNPair.RegularTree.ClassGraphBalls

/-!
# Radius-three fixation from neighboring radius-two fixers

Every vertex in a radius-three ball about `m`, other than `m`, is in a
radius-two ball about the first neighbor on a walk from `m`.  This elementary
cover is the graph step used to lift central middle fixation to the source
six-path radius-three hypothesis.
-/

public section
open Theory.GroupTheory.WeakBNPair.RegularTree
open SimpleGraph
variable {X V : Type*} [Group X] [MulAction X V]

theorem graphBallFixer_radius_three_of_neighbor
    (Γ : SimpleGraph V) (m : V) (z : X)
    (hz : z • m = m)
    (hN : ∀ v, Γ.Adj m v → z ∈ graphBallFixer Γ v 2) :
    z ∈ graphBallFixer Γ m 3 := by
  rw [mem_graphBallFixer]
  intro b hb
  have hdist : Γ.edist m b ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp : (3 : ℕ∞) ≠ ⊤) hb
  obtain ⟨p,hp⟩ := exists_walk_of_edist_ne_top hdist
  have hlen : p.length ≤ 3 := by
    have hh : (p.length : ℕ∞) ≤ (3 : ℕ∞) := hp ▸ hb
    exact ENat.natCast_le_natCast.mp hh
  cases p with
  | nil => exact hz
  | @cons _ v _ hmv q =>
      have hq : q.length ≤ 2 := by
        rw [Walk.length_cons] at hlen
        omega
      have hfix := (mem_graphBallFixer Γ v 2 z).mp (hN v hmv)
      apply hfix
      exact q.edist_le.trans (ENat.natCast_le_natCast.mpr hq)
