module
public import Theory.GroupTheory.CoprimeCentralizerDecomposition
public import Mathlib.GroupTheory.Nilpotent

/-!
# Displacement of a disjoint core by a cubic subgroup

When the fixed points of a cubic subgroup on R lie in C, an invariant
2-subgroup Q of R disjoint from C has full cubic commutator. If Q normalizes
K and the cubic lies in K, this forces Q into K.

This is the coprime-action calculation for the literal crossing core in
Aschbacher--Smith 2.5.7, final paragraph, printed p.556.
-/
public section

open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem disjoint_cubic_core_eq_commutator_le
    (R C Q K X : Subgroup G)
    (hQ : IsPGroup 2 Q) (hX : Nat.card X = 3)
    (hQR : Q ≤ R) (hXC : R ⊓ centralizer (X : Set G) ≤ C)
    (hdis : Disjoint Q C) (hXQ : X ≤ normalizer (Q : Set G))
    (hXK : X ≤ K) (hQK : Q ≤ normalizer (K : Set G)) :
    Q = ⁅Q, X⁆ ∧ Q ≤ K := by
  have hcop : Nat.Coprime (Nat.card X) (Nat.card Q) := by
    obtain ⟨n, hn⟩ := hQ.exists_card_eq
    rw [hX, hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  let : Group.IsNilpotent Q := hQ.isNilpotent
  have hfix : Q ⊓ centralizer (X : Set G) = ⊥ := by
    apply bot_unique
    exact (le_inf inf_le_left ((inf_le_inf hQR le_rfl).trans hXC)).trans hdis.le_bot
  have he := eq_commutator_sup_centralizer_of_solvable_coprime Q X hXQ inferInstance hcop
  rw [hfix, sup_bot_eq] at he
  refine ⟨he, he.le.trans ?_⟩
  exact (commutator_mono le_rfl hXK).trans
    (le_normalizer_iff_commutator_le_right.mp hQK)
end Subgroup
