module
public import Theory.GroupTheory.Commutator.RelativeGeneration
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Derived-order bounds for mutually normalizing subgroups

The derived subgroup of a normalized join lies in the product of the two
individual derived subgroups and their cross commutator. Each factor is
normal in the join, so two finite product-order estimates bound its order.
No ambient normality or centrality of these three factors is assumed.

Source application: MS93 (3.10) and (5.12), printed pp.879--881 and 927,
for the selected midpoint kernel joined to the entire residual core.
-/

public section
open scoped commutatorElement
namespace Subgroup

private theorem normalized_join_card_le {G : Type*} [Group G] [Finite G]
    (A B : Subgroup G) (hn : B ≤ normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) ≤ Nat.card A * Nat.card B := by
  rw [card_mul_eq_card_inf_mul_card_sup_of_normalizes A B hn]
  exact Nat.le_mul_of_pos_left _ (Nat.card_pos (α := (A ⊓ B : Subgroup G)))

/-- The derived subgroup of a join of mutually normalizing finite subgroups
is bounded by the product of their two derived orders and their cross order. -/
theorem commutator_sup_card_le_of_mutual_normalization
    {G : Type*} [Group G] [Finite G] (A B : Subgroup G)
    (hAB : A ≤ normalizer (B : Set G)) (hBA : B ≤ normalizer (A : Set G)) :
    Nat.card (⁅A ⊔ B,A ⊔ B⁆ : Subgroup G) ≤
      Nat.card (⁅A,A⁆ : Subgroup G) * Nat.card (⁅B,B⁆ : Subgroup G) *
        Nat.card (⁅A,B⁆ : Subgroup G) := by
  let J := A ⊔ B
  let D := (⁅A,A⁆ ⊔ ⁅B,B⁆) ⊔ ⁅A,B⁆
  have hJA : J ≤ normalizer (A : Set G) := sup_le A.le_normalizer hBA
  have hJB : J ≤ normalizer (B : Set G) := sup_le hAB B.le_normalizer
  have hnorm (P Q : Subgroup G)
      (hP : J ≤ normalizer (P : Set G)) (hQ : J ≤ normalizer (Q : Set G)) :
      J ≤ normalizer ((⁅P,Q⁆ : Subgroup G) : Set G) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hP hg),
      mem_normalizer_iff_map_conj_eq.mp (hQ hg)]
  have hAA := hnorm A A hJA hJA
  have hBB := hnorm B B hJB hJB
  have hcross := hnorm A B hJA hJB
  have hpair : J ≤ normalizer ((⁅A,A⁆ ⊔ ⁅B,B⁆ : Subgroup G) : Set G) :=
    (le_inf hAA hBB).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hJD : J ≤ normalizer (D : Set G) :=
    (le_inf hpair hcross).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hder : ⁅J,J⁆ ≤ D := by
    apply commutator_sup_le_of_relative_normal J A B J D hJD le_sup_left le_sup_right
    · rw [commutator_comm]
      apply commutator_sup_le_of_relative_normal J A B A D hJD le_sup_left le_sup_right
      · exact le_sup_left.trans le_sup_left
      · rw [commutator_comm]; exact le_sup_right
    · rw [commutator_comm]
      apply commutator_sup_le_of_relative_normal J A B B D hJD le_sup_left le_sup_right
      · exact le_sup_right
      · exact le_sup_right.trans le_sup_left
  have hcard := normalized_join_card_le (⁅A,A⁆ ⊔ ⁅B,B⁆) ⁅A,B⁆
    ((commutator_le_sup A B).trans hpair)
  have hpaircard := normalized_join_card_le ⁅A,A⁆ ⁅B,B⁆
    (((commutator_le_sup B B).trans (sup_le le_sup_right le_sup_right)).trans hAA)
  exact (card_le_of_le hder).trans (hcard.trans (Nat.mul_le_mul_right _ hpaircard))

end Subgroup
