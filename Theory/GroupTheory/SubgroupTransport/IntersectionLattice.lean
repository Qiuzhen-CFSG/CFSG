module
public import Theory.GroupTheory.SubgroupTransport.IntersectionRectangle
public import Mathlib.GroupTheory.Index

/-!
# Reconstruction from intersection indices

All cells on a diagonal of the partial-isomorphism rectangle have the same
order. The index between successive diagonals decreases with depth, by the
injection of subgroup coset spaces. Equality of consecutive indices forces
adjacent cells to generate their common predecessor. Consequently a lower
bound at a later diagonal reconstructs every intervening row.

This is the subgroup-join form of Niles, *Pushing-up in finite groups* (1979),
Lemma 2.7. No normality is needed for the join statement; source applications
can separately use the normality of the factors to identify their set product.
-/

public section
open Subgroup
namespace Theory.GroupTheory.SubgroupTransport
variable {G : Type*} [Group G] {S T : Subgroup G}

theorem intervalCell_antitone (φ : S ≃* T) {a b c d : ℕ} (hac : a ≤ c) (hbd : b ≤ d) :
    intervalCell φ c d ≤ intervalCell φ a b :=
  inf_le_inf (forwardChain_antitone φ hac) (forwardChain_antitone φ.symm hbd)

theorem card_intervalCell_shift (φ : S ≃* T) (a b : ℕ) :
    Nat.card (intervalCell φ (a + 1) b) = Nat.card (intervalCell φ a (b + 1)) := by
  rw [← image_intervalCell]
  exact (Nat.card_congr (imageEquiv φ _ (intervalCell_le_domain φ a b)).toEquiv).symm

/-- All cells on a diagonal have the same order. -/
theorem card_intervalCell (φ : S ≃* T) (a b : ℕ) :
    Nat.card (intervalCell φ a b) = Nat.card (intervalCell φ 0 (a + b)) := by
  induction a generalizing b with
  | zero => simp only [Nat.zero_add]
  | succ a ih =>
    simpa only [Nat.succ_add, Nat.add_succ] using
      (card_intervalCell_shift φ a b).trans (ih (b + 1))

@[expose] noncomputable def rectangleStepIndex (φ : S ≃* T) (n : ℕ) : ℕ :=
  (intervalCell φ 0 (n + 1)).relIndex (intervalCell φ 0 n)

private theorem card_mul_relIndex {A B : Subgroup G} (hAB : A ≤ B) :
    Nat.card A * A.relIndex B = Nat.card B := by
  simpa only [relIndex_bot_left] using relIndex_mul_relIndex (⊥ : Subgroup G) A B bot_le hAB

/-- Every adjacent inclusion has the index prescribed by its diagonal. -/
theorem intervalCell_relIndex [Finite G] (φ : S ≃* T) (a b c d : ℕ)
    (hac : a ≤ c) (hbd : b ≤ d) (hsum : c + d = a + b + 1) :
    (intervalCell φ c d).relIndex (intervalCell φ a b) = rectangleStepIndex φ (a + b) := by
  have h₁ := card_mul_relIndex (intervalCell_antitone φ hac hbd)
  have h₂ := card_mul_relIndex (intervalCell_antitone φ (a := 0) (c := 0)
    (b := a + b) (d := a + b + 1) le_rfl (Nat.le_succ _))
  rw [card_intervalCell φ c d, card_intervalCell φ a b, hsum] at h₁
  change _ * rectangleStepIndex φ (a + b) = _ at h₂
  exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := intervalCell φ 0 (a + b + 1)))
    (h₁.trans h₂.symm)

/-- The successive intersection indices decrease with depth. -/
theorem rectangleStepIndex_antitone [Finite G] (φ : S ≃* T) :
    Antitone (rectangleStepIndex φ) := by
  apply antitone_nat_of_succ_le
  intro n
  have hh := relIndex_le_of_le_right
    (intervalCell_antitone φ (a := 0) (c := 0) (b := n) (d := n + 1)
      le_rfl (Nat.le_succ n))
    (show (intervalCell φ 1 n).relIndex (intervalCell φ 0 n) ≠ 0 from index_ne_zero_of_finite)
  rw [← inf_relIndex_right, inf_comm, intervalCell_adjacent_inf] at hh
  rw [intervalCell_relIndex φ 0 (n + 1) 1 (n + 1) (by omega) le_rfl (by omega),
    intervalCell_relIndex φ 0 n 1 n (by omega) le_rfl (by omega)] at hh
  simpa only [Nat.zero_add] using hh

private theorem sup_eq_of_relIndex_le [Finite G] {A B U : Subgroup G}
    (hAU : A ≤ U) (hBU : B ≤ U) (hi : B.relIndex U ≤ B.relIndex A) : A ⊔ B = U := by
  have hs := sup_le hAU hBU
  have he : B.relIndex (A ⊔ B) = B.relIndex U := le_antisymm
    (relIndex_le_of_le_right hs index_ne_zero_of_finite)
    (hi.trans (relIndex_le_of_le_right le_sup_left index_ne_zero_of_finite))
  have hm := relIndex_mul_relIndex B (A ⊔ B) U le_sup_right hs
  rw [he] at hm
  have hp : 0 < B.relIndex U := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hu : (A ⊔ B).relIndex U = 1 := by nlinarith
  exact le_antisymm hs (relIndex_eq_one.mp hu)

/-- Equality of consecutive indices reconstructs the preceding cell. -/
theorem intervalCell_sup_of_stepIndex_eq [Finite G] (φ : S ≃* T) (a b : ℕ)
    (he : rectangleStepIndex φ (a + b + 1) = rectangleStepIndex φ (a + b)) :
    intervalCell φ a (b + 1) ⊔ intervalCell φ (a + 1) b = intervalCell φ a b := by
  apply sup_eq_of_relIndex_le
    (intervalCell_antitone φ le_rfl (Nat.le_succ _))
    (intervalCell_antitone φ (Nat.le_succ _) le_rfl)
  rw [← inf_relIndex_right (H := intervalCell φ (a + 1) b)
    (K := intervalCell φ a (b + 1)), inf_comm, intervalCell_adjacent_inf]
  rw [intervalCell_relIndex φ a b (a + 1) b (Nat.le_succ _) le_rfl (by omega),
    intervalCell_relIndex φ a (b + 1) (a + 1) (b + 1)
      (Nat.le_succ _) le_rfl (by omega)]
  simpa only [show a + (b + 1) = a + b + 1 by omega, he] using
    (le_refl (rectangleStepIndex φ (a + b)))

/-- Niles' lattice criterion: if a later step index is at least the first
one, all intermediate adjacent joins reconstruct their preceding cells. -/
theorem intervalCell_sup_of_stepIndex_lower [Finite G] (φ : S ≃* T) {w a b : ℕ}
    (hlo : 1 ≤ a + b) (hhi : a + b + 1 ≤ w)
    (hw : rectangleStepIndex φ 1 ≤ rectangleStepIndex φ w) :
    intervalCell φ a (b + 1) ⊔ intervalCell φ (a + 1) b = intervalCell φ a b := by
  apply intervalCell_sup_of_stepIndex_eq
  apply le_antisymm (rectangleStepIndex_antitone φ (Nat.le_succ _))
  exact (rectangleStepIndex_antitone φ hlo).trans
    (hw.trans (rectangleStepIndex_antitone φ hhi))

/-- Literal successive restrictions identify every cell with the leftmost
cell on its diagonal. -/
theorem intervalCell_diagonal_equiv (φ : S ≃* T) (a b : ℕ) :
    Nonempty (intervalCell φ a b ≃* intervalCell φ 0 (a + b)) := by
  induction a generalizing b with
  | zero =>
    exact ⟨MulEquiv.subgroupCongr (by rw [Nat.zero_add])⟩
  | succ a ih =>
    obtain ⟨e⟩ := ih (b + 1)
    let f : intervalCell φ a (b + 1) ≃* intervalCell φ (a + 1) b :=
      (imageEquiv φ _ (intervalCell_le_domain φ a b)).trans
        (MulEquiv.subgroupCongr (image_intervalCell φ a b))
    exact ⟨(f.symm.trans e).trans (MulEquiv.subgroupCongr (by
      congr 1
      omega))⟩

theorem intervalCell_equiv (φ : S ≃* T) {a b c d : ℕ} (hsum : a + b = c + d) :
    Nonempty (intervalCell φ a b ≃* intervalCell φ c d) := by
  obtain ⟨e⟩ := intervalCell_diagonal_equiv φ a b
  obtain ⟨f⟩ := intervalCell_diagonal_equiv φ c d
  exact ⟨(e.trans (MulEquiv.subgroupCongr (congrArg (intervalCell φ 0) hsum))).trans f.symm⟩


end Theory.GroupTheory.SubgroupTransport
