module
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic

/-!
# Generating an index-two subgroup by conjugate intersections

For a family of index-two subgroups of Q, suppose their common
intersection has index larger than four. Each member is then generated
by its intersections with two other, distinct members. If every such
intersection coincided, that common subgroup would have index four in Q,
contradicting the hypothesis.

The literal source application is to the H-conjugates of
O₂(H)∩O₂(X) in the cubic--quintic argument of Aschbacher--Smith14.2.20--21,
pp.988--989. The action on the elementary H-span bounds the common
intersection and supplies the hypothesis.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

private theorem inf_index_two {Q A B : Subgroup G}
    (hAQ : A ≤ Q) (hBQ : B ≤ Q) (hAi : A.relIndex Q = 2)
    (hBi : B.relIndex Q = 2) (hne : A ≠ B) :
    (A ⊓ B).relIndex A = 2 := by
  have hn : ¬ A ≤ B := by
    intro hab
    have hm := relIndex_mul_relIndex A B Q hab hBQ
    rw [hAi,hBi] at hm
    exact hne (le_antisymm hab (relIndex_eq_one.mp (by omega : A.relIndex B = 1)))
  rw [inf_relIndex_left]
  have hu : B.relIndex A ≤ 2 := by
    simpa only [hBi] using relIndex_le_of_le_right (H := B) hAQ (by rw [hBi]; decide)
  have hp : B.relIndex A ≠ 0 := index_ne_zero_of_finite
  have hn' : B.relIndex A ≠ 1 := fun he => hn (relIndex_eq_one.mp he)
  omega

/-- In a family of index-two subgroups whose common intersection has index
larger than four, two intersections with any chosen member generate that member. -/
theorem exists_pair_intersections_sup_of_small_iInf {I : Type*}
    (Q : Subgroup G) (A : I → Subgroup G)
    (hA : ∀ i, A i ≤ Q) (hi : ∀ i, (A i).relIndex Q = 2)
    (hsmall : 4 * Nat.card (⨅ i, A i : Subgroup G) < Nat.card Q) (j : I) :
    ∃ i k, A i ≠ A j ∧ A k ≠ A j ∧
      (A j ⊓ A i) ⊔ (A j ⊓ A k) = A j := by
  classical
  have hex : ∃ i, A i ≠ A j := by
    by_contra! he
    have hInf : (⨅ i, A i) = A j := le_antisymm (iInf_le _ j)
      (le_iInf fun i => (he i).ge)
    have hm := ((A j).subgroupOf Q).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe (hA j)).toEquiv] at hm
    change (A j).relIndex Q * Nat.card (A j) = Nat.card Q at hm
    rw [hi j] at hm
    rw [hInf] at hsmall
    omega
  obtain ⟨i,hiNe⟩ := hex
  let B := A j ⊓ A i
  have hBi : B.relIndex (A j) = 2 :=
    inf_index_two (hA j) (hA i) (hi j) (hi i) hiNe.symm
  have hex2 : ∃ k, A k ≠ A j ∧ A j ⊓ A k ≠ B := by
    by_contra! he
    have hBInf : B ≤ ⨅ k, A k := by
      apply le_iInf
      intro k
      by_cases hk : A k = A j
      · rw [hk]; exact inf_le_left
      · exact (he k hk).symm ▸ (show A j ⊓ A k ≤ A k from inf_le_right)
    have hm := (B.subgroupOf (A j)).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe (show B ≤ A j from inf_le_left)).toEquiv] at hm
    change B.relIndex (A j) * Nat.card B = Nat.card (A j) at hm
    rw [hBi] at hm
    have hQ := ((A j).subgroupOf Q).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe (hA j)).toEquiv] at hQ
    change (A j).relIndex Q * Nat.card (A j) = Nat.card Q at hQ
    rw [hi j] at hQ
    have hc := card_le_of_le hBInf
    omega
  obtain ⟨k,hkNe,hkB⟩ := hex2
  let C := A j ⊓ A k
  have hCi : C.relIndex (A j) = 2 :=
    inf_index_two (hA j) (hA k) (hi j) (hi k) hkNe.symm
  have hnot : ¬ C ≤ B := by
    intro hcb
    have hm := relIndex_mul_relIndex C B (A j) hcb inf_le_left
    rw [hBi,hCi] at hm
    exact hkB (le_antisymm hcb (relIndex_eq_one.mp (by omega : C.relIndex B = 1)))
  have hm := relIndex_mul_relIndex B (B ⊔ C) (A j) le_sup_left
    (sup_le inf_le_left inf_le_left)
  rw [hBi] at hm
  have hne : B.relIndex (B ⊔ C) ≠ 1 := fun he =>
    hnot (le_sup_right.trans (relIndex_eq_one.mp he))
  have hout : (B ⊔ C).relIndex (A j) = 1 := by
    rcases Nat.prime_mul_iff.mp (hm ▸ Nat.prime_two) with hh | hh
    · exact hh.2
    · exact (hne hh.2).elim
  exact ⟨i,k,hiNe,hkNe,le_antisymm (sup_le inf_le_left inf_le_left)
    (relIndex_eq_one.mp hout)⟩
end Subgroup
