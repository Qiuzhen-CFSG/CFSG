module
public import Glauberman.FixedNormalPairDiagramCenters
public import Glauberman.FixedNormalPairCenters

/-!
# Reconstruction through twice the elementary-row parameter

The exact center cells identify the fixed index of central omega with an
adjacent intersection index at depth 2v. The already proved counting theorem
makes that index four, the same as the original index. The decreasing-index
criterion therefore reconstructs every row through 2v - 1.

This proves the intermediate lattice-depth assertion in Niles, *Pushing-up
in finite groups* (1979), Proposition 4.6(g), using the established full
fixed index directly. The later extension to 3v - 1 is separate.
-/

public section
open Subgroup Theory.GroupTheory.SubgroupTransport
namespace Glauberman
variable {G : Type*} [Group G] [Finite G] {S T : Subgroup G} {φ : S ≃* T}

private theorem NumericalPair.full_omega_fixed_index (h : NumericalPair S T φ) :
    (omegaCenterIn (S ⊓ T) ⊓ centralizer (S : Set G)).relIndex
      (omegaCenterIn (S ⊓ T)) = 4 := by
  have hS : S ≠ ⊥ := by
    intro hb
    have hi := h.index_left
    rw [hb, relIndex_bot_right] at hi
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
theorem NumericalPair.rectangleStepIndex_double_eq_four (h : NumericalPair S T φ)
    (v : ℕ) (hv : 0 < v)
    (hzS : centerIn S = intervalCell φ v (v + 1))
    (hzQ : centerIn (S ⊓ T) = intervalCell φ v v) :
    rectangleStepIndex φ (2 * v) = 4 := by
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
theorem IntersectionPair.exists_double_lattice_center_cells (P : IntersectionPair G)
    (h : NumericalPair P.left P.right P.equiv) :
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
  obtain ⟨v, hv, hE, hS, hT, _, hzS, hzT, hzQ⟩ := P.exists_center_cells h
  have hi := h.rectangleStepIndex_double_eq_four v hv hzS hzQ
  refine ⟨v, hv, hE, hS, hT, ?_, hzS, hzT, hzQ⟩
  intro a b hab hbound
  apply intervalCell_sup_of_stepIndex_lower P.equiv hab (show a + b + 1 ≤ 2 * v by omega)
  rw [P.rectangleStepIndex_eq_four 0 h, hi]

end Glauberman
