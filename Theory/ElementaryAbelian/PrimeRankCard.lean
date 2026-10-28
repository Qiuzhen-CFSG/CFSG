module
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.PrimeRankInvolutionLift
public import Theory.ElementaryAbelian.Injective

/-!
# Cardinality and prime rank of an elementary abelian group

An elementary group itself attains the elementary subgroup rank bound.
Together with the existing prime-rank witness this identifies its order with
p to its prime rank, and its logarithmic rank with prime rank.
-/

public section
namespace IsElementaryAbelian
variable {p : ℕ} [Fact p.Prime]
variable (A : Type*) [Group A] [Finite A] [IsElementaryAbelian p A]

theorem card_eq_pow_primeRank : Nat.card A = p ^ primeRank p A := by
  apply le_antisymm
  · have ht : IsElementaryAbelian p (⊤ : Subgroup A) :=
      IsElementaryAbelian.of_injective (⊤ : Subgroup A).subtype Subtype.val_injective
    simpa only [Subgroup.card_top] using
      (primeRank_le_iff_elementary_card_le A).mp le_rfl ⊤ ht
  · obtain ⟨E, _, hE⟩ := exists_elementaryAbelian_card_primeRank (G := A) (p := p)
    exact hE ▸ E.card_le_card_group

theorem log_card_eq_primeRank : Nat.log p (Nat.card A) = primeRank p A := by
  rw [card_eq_pow_primeRank (p := p) A, Nat.log_pow (Fact.out : p.Prime).one_lt]

end IsElementaryAbelian
