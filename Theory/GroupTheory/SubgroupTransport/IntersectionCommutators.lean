module
public import Theory.GroupTheory.SubgroupTransport.IntersectionLattice

/-!
# Shifted commutator bounds in the intersection rectangle

Commutator containments transport along every permitted sequence of literal
restrictions of the subgroup isomorphism. If both original members normalize
the middle diagonal cell, transporting one normality bound back and
intersecting it with the other gives a deeper commutator bound.

Source: Niles, *Pushing-up in finite groups* (1979), Proposition 4.6(f),
printed pages 46–47. In its application the middle cell is the full center
of the common normal intersection.
-/

public section
open Subgroup
namespace Theory.GroupTheory.SubgroupTransport
variable {G : Type*} [Group G] {S T : Subgroup G}

theorem intervalCell_symm (φ : S ≃* T) (a b : ℕ) :
    intervalCell φ.symm a b = intervalCell φ b a := by
  simp only [intervalCell, MulEquiv.symm_symm, inf_comm]

theorem intervalCell_commutator_shift (φ : S ≃* T) (k a b c d e f : ℕ)
    (h : ⁅intervalCell φ a (b + k), intervalCell φ c (d + k)⁆ ≤
      intervalCell φ e (f + k)) :
    ⁅intervalCell φ (a + k) b, intervalCell φ (c + k) d⁆ ≤
      intervalCell φ (e + k) f := by
  induction k generalizing a c e with
  | zero => simpa only [Nat.add_zero] using h
  | succ k ih =>
    simp only [Nat.add_succ] at h
    have hm := image_mono φ h
    rw [image_commutator _ _ _ (intervalCell_le_domain φ a (b + k))
      (intervalCell_le_domain φ c (d + k))] at hm
    rw [image_intervalCell, image_intervalCell, image_intervalCell] at hm
    have hh := ih (a + 1) (c + 1) (e + 1) hm
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hh

theorem intervalCell_commutator_shift_back (φ : S ≃* T) (k a b c d e f : ℕ)
    (h : ⁅intervalCell φ (a + k) b, intervalCell φ (c + k) d⁆ ≤
      intervalCell φ (e + k) f) :
    ⁅intervalCell φ a (b + k), intervalCell φ c (d + k)⁆ ≤
      intervalCell φ e (f + k) := by
  have hh := intervalCell_commutator_shift φ.symm k b a d c f e
    (by simpa only [intervalCell_symm] using h)
  simpa only [intervalCell_symm] using hh

/-- Two normality bounds on a central diagonal cell give the deeper
commutator bound after transporting one of them back along the actual map. -/
theorem intervalCell_center_commutator_bound (φ : S ≃* T) (v : ℕ) (hv : 0 < v)
    (hS : S ≤ normalizer (intervalCell φ v v : Set G))
    (hT : T ≤ normalizer (intervalCell φ v v : Set G)) :
    ⁅intervalCell φ 0 (2 * v), intervalCell φ v v⁆ ≤ intervalCell φ v (2 * v) := by
  have hL : intervalCell φ 0 (2 * v) ≤ S := by
    rw [show 2 * v = (2 * v - 1) + 1 by omega]
    exact intervalCell_le_domain φ 0 (2 * v - 1)
  have hR : intervalCell φ (2 * v) 0 ≤ T := by
    rw [show 2 * v = (2 * v - 1) + 1 by omega]
    exact intervalCell_le_range φ (2 * v - 1) 0
  have hs := le_normalizer_iff_commutator_le_right.mp (hL.trans hS)
  have ht := le_normalizer_iff_commutator_le_right.mp (hR.trans hT)
  have hm := intervalCell_commutator_shift_back φ v v 0 0 v 0 v (by
    simpa only [Nat.zero_add, show v + v = 2 * v by omega] using ht)
  have hm' : ⁅intervalCell φ 0 (2 * v), intervalCell φ v v⁆ ≤
      intervalCell φ 0 (2 * v) := by
    simpa only [Nat.zero_add, show v + v = 2 * v by omega, commutator_comm] using hm
  have hi := le_inf hm' hs
  rw [intervalCell_inf, max_eq_right (Nat.zero_le v),
    max_eq_left (show v ≤ 2 * v by omega)] at hi
  exact hi

end Theory.GroupTheory.SubgroupTransport
