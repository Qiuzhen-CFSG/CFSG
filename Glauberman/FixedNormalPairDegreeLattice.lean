module
public import Glauberman.FixedNormalPairDegree
public import Glauberman.FixedNormalPairDiagramCenters

/-!
# Original-degree center cells and reconstruction

The first elementary intersection has maximum abelian order in both
original members. Its diagonal therefore identifies both centers and the
center of their intersection. Sharp fixed index q then reconstructs the
whole diagram through twice the elementary-row parameter. No reduction of
the original field degree or deletion of a central attachment is used.

Source: Niles, *Pushing-up in finite groups* (1979), Proposition 4.6(a--g),
printed pp.46--47, through the depth-2v reconstruction. The later depth-3v
and nilpotence arguments still require their source proofs.
-/

public section
open Subgroup Theory.GroupTheory.SubgroupTransport
namespace Glauberman
variable {G : Type*} [Group G] [Finite G] {q : ℕ} {S T : Subgroup G} {φ : S ≃* T}

/-- The next left index remains q even at the elementary terminal step. -/
theorem NumericalPairAt.next_index_left {S T : Subgroup G} {φ : S ≃* T}
    (h : NumericalPairAt q S T φ) :
    (image φ.symm (S ⊓ T) ⊓ (S ⊓ T)).relIndex (image φ.symm (S ⊓ T)) = q := by
  let R := image φ.symm (S ⊓ T)
  have hRS : R ≤ S := image_le φ.symm _
  let _ : ((S ⊓ T).subgroupOf S).Normal := normal_subgroupOf_of_le_normalizer h.normal_left
  have hh := relIndex_sup_right (R.subgroupOf S) ((S ⊓ T).subgroupOf S)
  rw [← subgroupOf_sup hRS inf_le_left, relIndex_subgroupOf (sup_le hRS inf_le_left),
    h.next_generates, relIndex_subgroupOf hRS] at hh
  rw [inf_relIndex_left]
  exact hh.symm.trans h.index_left

namespace IntersectionPair

theorem numerical_row_before_first_elementary_at (P : IntersectionPair G)
    (h : NumericalPairAt q P.left P.right P.equiv) (n : ℕ)
    (hne : ∀ m < n, ¬ IsElementaryAbelian 2 ↥((P.row m).left ⊓ (P.row m).right)) :
    NumericalPairAt q (P.row n).left (P.row n).right (P.row n).equiv := by
  induction n with
  | zero => exact h
  | succ n ih =>
    have hn := ih (fun m hm => hne m (by omega))
    rcases hn.recursion with hE | ⟨hnext, _⟩
    · exact (hne n (Nat.lt_succ_self n) hE).elim
    · rw [row_succ_next]
      exact hnext

theorem rectangleStepIndex_eq_index (P : IntersectionPair G) (n : ℕ)
    (h : NumericalPairAt q (P.row n).left (P.row n).right (P.row n).equiv) :
    rectangleStepIndex P.equiv (n + 1) = q := by
  have hi := h.index_left
  rw [row_intersection_cell, (row_left_right_cells P n).1,
    intervalCell_relIndex P.equiv 0 (n + 1) 1 (n + 1) (by omega) le_rfl (by omega)] at hi
  simpa only [Nat.zero_add] using hi

theorem rectangleStepIndex_next_eq_index (P : IntersectionPair G) (n : ℕ)
    (h : NumericalPairAt q (P.row n).left (P.row n).right (P.row n).equiv) :
    rectangleStepIndex P.equiv (n + 2) = q := by
  have hi := h.next_index_left
  change ((P.row n).next.left ⊓ (P.row n).next.right).relIndex (P.row n).next.left = q at hi
  rw [← row_succ_next, row_intersection_cell, (row_left_right_cells P (n + 1)).1,
    intervalCell_relIndex P.equiv 0 (n + 1 + 1) 1 (n + 1 + 1)
      (by omega) le_rfl (by omega)] at hi
  simpa only [Nat.zero_add] using hi

/-- The first elementary intersection retains the maximum abelian order
in both original members and the numerical hypotheses at its preceding pair. -/
theorem exists_first_elementary_maximum_row_at (P : IntersectionPair G)
    (h : NumericalPairAt q P.left P.right P.equiv) :
    ∃ n, let Q := (P.row n).left ⊓ (P.row n).right
      IsElementaryAbelian 2 Q ∧ Q ∈ thompsonAbelianSubgroups P.left ∧
        Q ∈ thompsonAbelianSubgroups P.right ∧
        NumericalPairAt q (P.row n).left (P.row n).right (P.row n).equiv ∧
        ∀ m < n, ¬ IsElementaryAbelian 2 ↥((P.row m).left ⊓ (P.row m).right) := by
  classical
  generalize he : Nat.card P.left = m
  induction m using Nat.strong_induction_on generalizing P with
  | h m ih =>
    obtain ⟨hfamilyS, hfamilyT⟩ := h.maximum_families
    by_cases hE : IsElementaryAbelian 2 ↥(P.left ⊓ P.right)
    · let _ := hE
      have hmax : P.left ⊓ P.right ∈ thompsonAbelianSubgroups (P.left ⊓ P.right) :=
        ⟨le_rfl, inferInstance, fun _ hle _ => card_le_of_le hle⟩
      exact ⟨0, hE, hfamilyS hmax, hfamilyT hmax, h, fun _ hm => by omega⟩
    · obtain ⟨hnext, _⟩ := h.recursion.resolve_left hE
      obtain ⟨n, hEn, hmaxS, hmaxT, hnum, hminimal⟩ :=
        ih (Nat.card P.next.left) (he ▸ P.next_card_lt_at h) P.next hnext rfl
      refine ⟨n + 1, hEn, hfamilyS hmaxT, hfamilyT hmaxT, hnum, ?_⟩
      intro j hj
      cases j with
      | zero => exact hE
      | succ j => exact hminimal j (by omega)


end IntersectionPair
/-- Finite descent supplies the exact center cells under the numerical
pair hypotheses, including their common elementary-row parameter. -/
theorem IntersectionPair.exists_center_cells_at (P : IntersectionPair G)
    (h : NumericalPairAt q P.left P.right P.equiv) :
    ∃ v : ℕ, 0 < v ∧
      IsElementaryAbelian 2 ↥(intervalCell P.equiv 1 v) ∧
      intervalCell P.equiv 1 v ∈ thompsonAbelianSubgroups P.left ∧
      intervalCell P.equiv 1 v ∈ thompsonAbelianSubgroups P.right ∧
      (∀ a b : ℕ, 1 ≤ a + b → a + b ≤ v →
        intervalCell P.equiv a (b + 1) ⊔ intervalCell P.equiv (a + 1) b =
          intervalCell P.equiv a b) ∧
      centerIn P.left = intervalCell P.equiv v (v + 1) ∧
      centerIn P.right = intervalCell P.equiv (v + 1) v ∧
      centerIn (P.left ⊓ P.right) = intervalCell P.equiv v v := by
  obtain ⟨n, hE, hS, hT, hnum, _⟩ := P.exists_first_elementary_maximum_row_at h
  rw [P.row_intersection_cell] at hE hS hT
  let _ := hE
  have hi := P.rectangleStepIndex_next_eq_index n hnum
  have hgen : ∀ a b : ℕ, 1 ≤ a + b → a + b ≤ n + 1 →
      intervalCell P.equiv a (b + 1) ⊔ intervalCell P.equiv (a + 1) b =
        intervalCell P.equiv a b := by
    intro a b hab hbound
    apply intervalCell_sup_of_stepIndex_lower P.equiv hab (show a + b + 1 ≤ n + 2 by omega)
    rw [P.rectangleStepIndex_eq_index 0 h, hi]
  exact ⟨n + 1, by omega, hE, hS, hT, hgen,
    centers_eq_cells_of_elementary_maximum_lattice P.equiv (n + 1) (by omega) hS hT hgen⟩

private theorem NumericalPairAt.full_omega_fixed_index (h : NumericalPairAt q S T φ) :
    (omegaCenterIn (S ⊓ T) ⊓ centralizer (S : Set G)).relIndex
      (omegaCenterIn (S ⊓ T)) = q := by
  have hS : S ≠ ⊥ := by
    intro hb
    have hi := h.index_left
    rw [hb, relIndex_bot_right] at hi
    have := h.nontrivial_index
    omega
  obtain ⟨_, _, _, _, _, _, hi, _⟩ :=
    fixed_normal_pair_counting S T (omegaCenterIn (S ⊓ T)) φ hS h.no_fixed
      h.normal_left h.normal_right
      (fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).1) inferInstance
      (fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).2.1)
      (fun B hB hBQ => by rw [h.index_left]; exact h.lower_left B hB.1 hBQ)
      (fun B hB hBQ => by rw [h.index_right]; exact h.lower_right B hB.1 hBQ)
  exact hi.trans h.index_left

/-- The already established fixed index and exact center cells extend the
constant intersection index to twice the elementary-row parameter. -/
theorem NumericalPairAt.rectangleStepIndex_double_eq_index (h : NumericalPairAt q S T φ)
    (v : ℕ) (hv : 0 < v)
    (hzS : centerIn S = intervalCell φ v (v + 1))
    (hzQ : centerIn (S ⊓ T) = intervalCell φ v v) :
    rectangleStepIndex φ (2 * v) = q := by
  have hzSQ : centerIn S ≤ S ⊓ T := by
    rw [hzS, ← intervalCell_intersection φ]
    exact intervalCell_antitone φ (by omega) (by omega)
  have hfixed := omegaCenterIn_eq_inf_of_center_le (S ⊓ T) S inf_le_left hzSQ
  obtain ⟨hωS, _, hωQ⟩ := h.omegaCenters_eq_centers
  rw [hωS, hωQ] at hfixed
  have hi := h.full_omega_fixed_index
  rw [hωQ, ← hfixed, hzS, hzQ,
    intervalCell_relIndex φ v v v (v + 1) le_rfl (Nat.le_succ v) (by omega)] at hi
  simpa only [show v + v = 2 * v by omega] using hi

/-- The same elementary maximum cell and exact centers reconstruct every
adjacent join through printed row 2v - 1. -/
theorem IntersectionPair.exists_double_lattice_center_cells_at (P : IntersectionPair G)
    (h : NumericalPairAt q P.left P.right P.equiv) :
    ∃ v : ℕ, 0 < v ∧
      IsElementaryAbelian 2 ↥(intervalCell P.equiv 1 v) ∧
      intervalCell P.equiv 1 v ∈ thompsonAbelianSubgroups P.left ∧
      intervalCell P.equiv 1 v ∈ thompsonAbelianSubgroups P.right ∧
      (∀ a b : ℕ, 1 ≤ a + b → a + b < 2 * v →
        intervalCell P.equiv a (b + 1) ⊔ intervalCell P.equiv (a + 1) b =
          intervalCell P.equiv a b) ∧
      centerIn P.left = intervalCell P.equiv v (v + 1) ∧
      centerIn P.right = intervalCell P.equiv (v + 1) v ∧
      centerIn (P.left ⊓ P.right) = intervalCell P.equiv v v := by
  obtain ⟨v, hv, hE, hS, hT, _, hzS, hzT, hzQ⟩ := P.exists_center_cells_at h
  have hi := h.rectangleStepIndex_double_eq_index v hv hzS hzQ
  refine ⟨v, hv, hE, hS, hT, ?_, hzS, hzT, hzQ⟩
  intro a b hab hbound
  apply intervalCell_sup_of_stepIndex_lower P.equiv hab (show a + b + 1 ≤ 2 * v by omega)
  rw [P.rectangleStepIndex_eq_index 0 h, hi]


end Glauberman
