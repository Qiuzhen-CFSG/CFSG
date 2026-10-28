module
public import Theory.SpecificGroups.Alternating.EightNineInvolutionCounts.Basic

/-!
# Summing the restricted mixed-pair count one row at a time

A product subtype is equivalent to the sum of its row subtypes. This keeps
finite certificates small while preserving the ordered-pair convention.
-/

namespace alternatingGroup.EightNineInvolutionCounts
open Theory.GroupTheory.TwoInvolutionClassOrder

public theorem kappa_eq_sum {G : Type*} [Group G] [Finite G] {r s : ℕ}
    (z v u : G) (hz : orderOf z = 2) (hv : orderOf v = 2) (hn : ¬ IsConj z v)
    (a : Fin r ≃ CentralizerClass z u) (b : Fin s ≃ CentralizerClass v u)
    (P : Fin r → Fin s → Prop) [DecidableRel P]
    (hp : ∀ i j, halfOrder ((a i).val : G) ((b j).val : G) = u ↔ P i j) :
    kappa z v u = ∑ i : Fin r, (Finset.univ.filter (P i)).card := by
  rw [kappa_eq_card z v u hz hv hn a b]
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun p : Fin r × Fin s => hp p.1 p.2))]
  let e : {p : Fin r × Fin s // P p.1 p.2} ≃ (Σ i : Fin r, {j : Fin s // P i j}) := {
    toFun := fun p => ⟨p.val.1, ⟨p.val.2, p.property⟩⟩
    invFun := fun p => ⟨(p.1, p.2.val), p.2.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]

end alternatingGroup.EightNineInvolutionCounts
