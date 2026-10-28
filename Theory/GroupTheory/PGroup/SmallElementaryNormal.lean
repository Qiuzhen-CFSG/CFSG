module

public import Theory.GroupTheory.Commutator.TwoSubgroupNormalizer
public import Theory.ElementaryAbelian.Basic

/-!
# Commutators of small normal elementary subgroups

A normal elementary abelian two-subgroup of order at most four in a finite
two-group has central commutator with the whole group. This is the abstract
small-subgroup step used after the bound on `Ω₁(Z(B))` in Stellmacher (6.3),
journal p.31 (`refs/latex/stellmacher-n-group.tex`). Combined with the exponent
two property, centrality places that commutator in `Ω₁(Z(S))` in the source
application.

The proof uses the full-commutator obstruction for finite p-groups: a
nontrivial normal subgroup cannot equal its commutator with the ambient
group. Thus commutation strictly reduces its order. Starting at order at
most four, the first commutator has order at most two, since its order is
one or divisible by two; the next commutator is trivial. The elementary
abelian hypothesis records the intended interface, although this centrality
argument itself only needs normality and the order bound.
-/

namespace Subgroup

/-- The commutator of a normal elementary subgroup of order at most four
with a finite two-group is central. -/
public theorem commutator_le_center_of_elementary_card_le_four
    {G : Type*} [Group G] [Finite G] (hG : IsPGroup 2 G)
    (A : Subgroup G) [A.Normal] [IsElementaryAbelian 2 A]
    (hA : Nat.card A ≤ 4) : ⁅A, (⊤ : Subgroup G)⁆ ≤ center G := by
  have hdrop (H : Subgroup G) [H.Normal] (hne : H ≠ ⊥) :
      Nat.card (⁅H, (⊤ : Subgroup G)⁆ : Subgroup G) < Nat.card H := by
    apply Nat.lt_of_not_ge
    intro hcard
    have heq : ⁅H, (⊤ : Subgroup G)⁆ = H :=
      eq_of_le_of_card_ge (commutator_le_left H ⊤) hcard
    exact hne (bot_unique (le_normal_of_quotient_isPGroup_of_eq_commutator
      H ⊤ ⊥ (hG.to_quotient ⊥) heq))
  by_cases hAbot : A = ⊥
  · simp [hAbot]
  let C := ⁅A, (⊤ : Subgroup G)⁆
  have hCcard : Nat.card C ≤ 2 := by
    have hlt := hdrop A hAbot
    change Nat.card C < Nat.card A at hlt
    rcases (hG.to_subgroup C).card_eq_or_dvd with hone | heven
    · omega
    · omega
  apply commutator_top_right_eq_bot_iff_le_center.mp
  change ⁅C, (⊤ : Subgroup G)⁆ = ⊥
  by_cases hCbot : C = ⊥
  · simp [hCbot]
  exact eq_bot_of_card_le _ (by have hlt := hdrop C hCbot; omega)

end Subgroup
