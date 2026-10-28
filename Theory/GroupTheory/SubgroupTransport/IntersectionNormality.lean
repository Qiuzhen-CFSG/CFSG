module
public import Theory.GroupTheory.SubgroupTransport.IntervalDiagram

/-!
# Normality and endpoint commutators in an intersection diagram

Normality of the original common intersection propagates down the left
boundary: both children are normal in their parent, and their intersection
is normal in each child. Literal isomorphism shifts give the same assertion
at every non-root cell. Consequently a proper interval normalizes both
endpoint deletions, so its endpoint commutator lies in their intersection.

Source: Niles, *Pushing-up in finite groups* (1979), Lemma 5.1, printed p.49.
This proof needs no numerical pair hypothesis or reconstruction identity.
-/

public section
open Subgroup
namespace Theory.GroupTheory.SubgroupTransport
variable {G : Type*} [Group G] {S T : Subgroup G}

private theorem normalized_inf_of_normalized {A B C : Subgroup G}
    (hBA : B ≤ A) (hCA : C ≤ A)
    (hB : ⁅A, B⁆ ≤ B) (hC : ⁅A, C⁆ ≤ C) :
    ⁅B, B ⊓ C⁆ ≤ B ⊓ C ∧ ⁅C, B ⊓ C⁆ ≤ B ⊓ C :=
  ⟨le_inf ((commutator_mono hBA inf_le_left).trans hB)
      ((commutator_mono hBA inf_le_right).trans hC),
    le_inf ((commutator_mono hCA inf_le_left).trans hB)
      ((commutator_mono hCA inf_le_right).trans hC)⟩

private theorem intervalCell_boundary_normal (φ : S ≃* T)
    (hS : S ≤ normalizer (S ⊓ T : Set G))
    (hT : T ≤ normalizer (S ⊓ T : Set G)) (n : ℕ) :
    ⁅intervalCell φ 0 (n + 1), intervalCell φ 0 (n + 2)⁆ ≤ intervalCell φ 0 (n + 2) ∧
      ⁅intervalCell φ 0 (n + 1), intervalCell φ 1 (n + 1)⁆ ≤ intervalCell φ 1 (n + 1) := by
  induction n with
  | zero =>
    constructor
    · have hh := intervalCell_commutator_shift_back φ 1 0 0 0 1 0 1 (by
        simpa only [Nat.zero_add, intervalCell_initial_right, intervalCell_intersection] using
          le_normalizer_iff_commutator_le_right.mp hT)
      simpa only [Nat.zero_add] using hh
    · simpa only [Nat.zero_add, intervalCell_initial_left, intervalCell_intersection] using
        le_normalizer_iff_commutator_le_right.mp hS
  | succ n ih =>
    have hh := normalized_inf_of_normalized
      (intervalCell_antitone φ (a := 0) (b := n + 1) le_rfl (show n + 1 ≤ n + 2 by omega))
      (intervalCell_antitone φ (a := 0) (b := n + 1) (show 0 ≤ 1 by omega) le_rfl)
      ih.1 ih.2
    rw [intervalCell_inf, max_eq_right (show 0 ≤ 1 by omega),
      max_eq_left (show n + 1 ≤ n + 2 by omega)] at hh
    constructor
    · have hm := intervalCell_commutator_shift_back φ 1 0 (n + 1) 0 (n + 2) 0 (n + 2)
        (by simpa only [Nat.zero_add] using hh.2)
      simpa only [Nat.add_assoc] using hm
    · simpa only [Nat.add_assoc] using hh.1

/-- Normality of the common intersection in both original members
propagates to every pair of adjacent descendants of a non-root cell. -/
theorem intervalCell_normalizes_successors (φ : S ≃* T)
    (hS : S ≤ normalizer (S ⊓ T : Set G))
    (hT : T ≤ normalizer (S ⊓ T : Set G)) (a b : ℕ) (hab : 1 ≤ a + b) :
    intervalCell φ a b ≤ normalizer (intervalCell φ a (b + 1) : Set G) ∧
      intervalCell φ a b ≤ normalizer (intervalCell φ (a + 1) b : Set G) := by
  have hh := intervalCell_boundary_normal φ hS hT (a + b - 1)
  rw [show a + b - 1 + 1 = a + b by omega,
    show a + b - 1 + 2 = a + b + 1 by omega] at hh
  constructor
  · apply le_normalizer_iff_commutator_le_right.mpr
    have hm := intervalCell_commutator_shift φ a 0 b 0 (b + 1) 0 (b + 1) (by
      simpa only [show b + a = a + b by omega,
        show b + 1 + a = a + b + 1 by omega] using hh.1)
    simpa only [Nat.zero_add] using hm
  · apply le_normalizer_iff_commutator_le_right.mpr
    have hm := intervalCell_commutator_shift φ a 0 b 1 b 1 b (by
      simpa only [show b + a = a + b by omega] using hh.2)
    simpa only [Nat.zero_add, show 1 + a = a + 1 by omega] using hm

/-- Each proper interval normalizes the intervals obtained by deleting
either endpoint. -/
theorem intervalDiagram_normalizes_trim (φ : S ≃* T)
    (hS : S ≤ normalizer (S ⊓ T : Set G))
    (hT : T ≤ normalizer (S ⊓ T : Set G)) (w : ℕ) {i j : ℕ}
    (hij : i < j) (hjw : j ≤ w) (hproper : j < i + w) :
    intervalDiagram φ w i j ≤ normalizer (intervalDiagram φ w i (j - 1) : Set G) ∧
      intervalDiagram φ w i j ≤ normalizer (intervalDiagram φ w (i + 1) j : Set G) := by
  simpa only [intervalDiagram, show w - (j - 1) = w - j + 1 by omega] using
    intervalCell_normalizes_successors φ hS hT i (w - j) (by omega)

/-- Endpoint commutators lie in the interval with both endpoints removed.
This is the normality argument of Niles Lemma 5.1. -/
theorem intervalDiagram_endpoint_commutator_le (φ : S ≃* T)
    (hS : S ≤ normalizer (S ⊓ T : Set G))
    (hT : T ≤ normalizer (S ⊓ T : Set G)) (w : ℕ) {i j : ℕ}
    (hij : i < j) (hjw : j ≤ w) (hproper : j < i + w) :
    ⁅intervalDiagram φ w i i, intervalDiagram φ w j j⁆ ≤
      intervalDiagram φ w (i + 1) (j - 1) := by
  obtain ⟨hleft, hright⟩ := intervalDiagram_normalizes_trim φ hS hT w hij hjw hproper
  have hl : ⁅intervalDiagram φ w i i, intervalDiagram φ w j j⁆ ≤
      intervalDiagram φ w i (j - 1) :=
    (commutator_mono (intervalDiagram_mono φ le_rfl (show i ≤ j - 1 by omega))
      (intervalDiagram_mono φ (show i ≤ j by omega) le_rfl)).trans
      (le_normalizer_iff_commutator_le_left.mp hleft)
  have hr : ⁅intervalDiagram φ w i i, intervalDiagram φ w j j⁆ ≤
      intervalDiagram φ w (i + 1) j :=
    (commutator_mono (intervalDiagram_mono φ le_rfl (show i ≤ j by omega))
      (intervalDiagram_mono φ (show i + 1 ≤ j by omega) le_rfl)).trans
      (le_normalizer_iff_commutator_le_right.mp hright)
  have hh := le_inf hl hr
  rw [intervalDiagram_inf, max_eq_right (show i ≤ i + 1 by omega),
    min_eq_left (show j - 1 ≤ j by omega)] at hh
  exact hh

end Theory.GroupTheory.SubgroupTransport
