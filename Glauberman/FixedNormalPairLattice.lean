module
public import Glauberman.FixedNormalPairRectangle
public import Glauberman.FixedNormalPairGeneration
public import Theory.GroupTheory.SubgroupTransport.IntersectionLattice

/-!
# Reconstruction through the first elementary intersection row

The relative index in the next restricted pair remains four even at the
terminal elementary step. Before the first elementary intersection, the
numerical pair hypotheses continue to hold. Applying the decreasing-index
criterion therefore reconstructs every adjacent join through that row.

Source: Niles, *Pushing-up in finite groups* (1979), Proposition 4.6(a) and
the first lattice-depth assertion in its proof, printed page 46. Extending
the lattice to depth 3v - 1 uses later module and commutator arguments.
-/

public section
open Subgroup Theory.GroupTheory.SubgroupTransport
namespace Glauberman
variable {G : Type*} [Group G] [Finite G]

/-- The next left index remains four even at the elementary terminal step. -/
theorem NumericalPair.next_index_left {S T : Subgroup G} {φ : S ≃* T}
    (h : NumericalPair S T φ) :
    (image φ.symm (S ⊓ T) ⊓ (S ⊓ T)).relIndex (image φ.symm (S ⊓ T)) = 4 := by
  let R := image φ.symm (S ⊓ T)
  have hRS : R ≤ S := image_le φ.symm _
  let _ : ((S ⊓ T).subgroupOf S).Normal := normal_subgroupOf_of_le_normalizer h.normal_left
  have hh := relIndex_sup_right (R.subgroupOf S) ((S ⊓ T).subgroupOf S)
  rw [← subgroupOf_sup hRS inf_le_left, relIndex_subgroupOf (sup_le hRS inf_le_left),
    h.next_generates, relIndex_subgroupOf hRS] at hh
  rw [inf_relIndex_left]
  exact hh.symm.trans h.index_left

namespace IntersectionPair

theorem numerical_row_before_first_elementary (P : IntersectionPair G)
    (h : NumericalPair P.left P.right P.equiv) (n : ℕ)
    (hne : ∀ m < n, ¬ IsElementaryAbelian 2 ↥((P.row m).left ⊓ (P.row m).right)) :
    NumericalPair (P.row n).left (P.row n).right (P.row n).equiv := by
  induction n with
  | zero => exact h
  | succ n ih =>
    have hn := ih (fun m hm => hne m (by omega))
    rcases hn.recursion with hE | ⟨hnext, _⟩
    · exact (hne n (Nat.lt_succ_self n) hE).elim
    · rw [row_succ_next]
      exact hnext

theorem rectangleStepIndex_eq_four (P : IntersectionPair G) (n : ℕ)
    (h : NumericalPair (P.row n).left (P.row n).right (P.row n).equiv) :
    rectangleStepIndex P.equiv (n + 1) = 4 := by
  have hi := h.index_left
  rw [row_intersection_cell, (row_left_right_cells P n).1,
    intervalCell_relIndex P.equiv 0 (n + 1) 1 (n + 1) (by omega) le_rfl (by omega)] at hi
  simpa only [Nat.zero_add] using hi

theorem rectangleStepIndex_next_eq_four (P : IntersectionPair G) (n : ℕ)
    (h : NumericalPair (P.row n).left (P.row n).right (P.row n).equiv) :
    rectangleStepIndex P.equiv (n + 2) = 4 := by
  have hi := h.next_index_left
  change ((P.row n).next.left ⊓ (P.row n).next.right).relIndex (P.row n).next.left = 4 at hi
  rw [← row_succ_next, row_intersection_cell, (row_left_right_cells P (n + 1)).1,
    intervalCell_relIndex P.equiv 0 (n + 1 + 1) 1 (n + 1 + 1)
      (by omega) le_rfl (by omega)] at hi
  simpa only [Nat.zero_add] using hi

/-- Finite descent reconstructs the entire diagram through its first
elementary row. The integer v is the printed elementary-row parameter. -/
theorem exists_elementary_lattice_row (P : IntersectionPair G)
    (h : NumericalPair P.left P.right P.equiv) :
    ∃ v : ℕ, 0 < v ∧ IsElementaryAbelian 2 ↥(intervalCell P.equiv 1 v) ∧
      rectangleStepIndex P.equiv (v + 1) = 4 ∧
      ∀ a b : ℕ, 1 ≤ a + b → a + b ≤ v →
        intervalCell P.equiv a (b + 1) ⊔ intervalCell P.equiv (a + 1) b =
          intervalCell P.equiv a b := by
  classical
  have hex := exists_elementary_row P h
  let n := Nat.find hex
  have hn : NumericalPair (P.row n).left (P.row n).right (P.row n).equiv :=
    numerical_row_before_first_elementary P h n (fun m hm => Nat.find_min hex hm)
  have hE := Nat.find_spec hex
  change IsElementaryAbelian 2 ↥((P.row n).left ⊓ (P.row n).right) at hE
  rw [row_intersection_cell] at hE
  have hi := rectangleStepIndex_next_eq_four P n hn
  refine ⟨n + 1, by omega, hE, hi, ?_⟩
  intro a b hab hbound
  apply intervalCell_sup_of_stepIndex_lower P.equiv hab (show a + b + 1 ≤ n + 2 by omega)
  rw [rectangleStepIndex_eq_four P 0 h, hi]

/-- The first elementary intersection retains the maximum abelian order
in both original members and the numerical hypotheses at its preceding pair. -/
theorem exists_first_elementary_maximum_row (P : IntersectionPair G)
    (h : NumericalPair P.left P.right P.equiv) :
    ∃ n, let Q := (P.row n).left ⊓ (P.row n).right
      IsElementaryAbelian 2 Q ∧ Q ∈ thompsonAbelianSubgroups P.left ∧
        Q ∈ thompsonAbelianSubgroups P.right ∧
        NumericalPair (P.row n).left (P.row n).right (P.row n).equiv ∧
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
        ih (Nat.card P.next.left) (he ▸ P.next_card_lt h) P.next hnext rfl
      refine ⟨n + 1, hEn, hfamilyS hmaxT, hfamilyT hmaxT, hnum, ?_⟩
      intro j hj
      cases j with
      | zero => exact hE
      | succ j => exact hminimal j (by omega)


end IntersectionPair
end Glauberman
