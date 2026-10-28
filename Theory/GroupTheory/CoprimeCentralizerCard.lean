module
public import Theory.GroupTheory.CoprimeCentralizerDirectProduct
public import Theory.GroupTheory.SubgroupProductCard

/-!
# Orders of fixed and moved subgroups under coprime conjugation

Coprime splitting of a finite abelian subgroup gives a direct product of
its literal ambient commutator and centralizer. The finite subgroup product
formula therefore computes the centralizer order from the original group
and moved-subgroup orders. This is the order calculation in
Aschbacher–Smith 10.2.3(4), printed p.746.
-/

public section
open Subgroup
open scoped IsMulCommutative Pointwise

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Orders multiply in the actual coprime fixed/moved decomposition. -/
theorem commutator_card_mul_centralizer_card (E P : Subgroup G) [IsMulCommutative E]
    (hn : P ≤ normalizer (E : Set G))
    (hc : Nat.Coprime (Nat.card P) (Nat.card E)) :
    Nat.card (⁅E,P⁆ : Subgroup G) * Nat.card (E ⊓ centralizer (P : Set G) : Subgroup G) = Nat.card E := by
  let C := E ⊓ centralizer (P : Set G)
  have hME : ⁅E,P⁆ ≤ E := le_normalizer_iff_commutator_le_left.mp hn
  have hMC : ⁅E,P⁆ ≤ normalizer (C : Set G) := by
    apply le_trans _ (centralizer_le_normalizer _)
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm (⟨y,hy.1⟩ : E) ⟨x,hME hx⟩)
  have hprod : ((⁅E,P⁆ : Subgroup G) : Set G) * (C : Set G) = E := by
    rw [← coe_mul_of_left_le_normalizer_right ⁅E,P⁆ C hMC]
    congr 1
    exact (eq_commutator_sup_centralizer_of_solvable_coprime E P hn
      (Group.isSolvable_of_comm fun x y => mul_comm x y) hc).symm
  have hd : ⁅E,P⁆ ⊓ C = ⊥ := (commutator_disjoint_centralizer_of_coprime E P hn hc).eq_bot
  have hh := card_set_mul_mul_card_inf ⁅E,P⁆ C
  rw [hprod,hd,Nat.card_unique (α := (⊥ : Subgroup G)),mul_one] at hh
  exact hh.symm

/-- Binary group and displacement orders determine the centralizer order. -/
theorem centralizer_card_of_binary_moved_order (E P : Subgroup G) [IsMulCommutative E]
    (hn : P ≤ normalizer (E : Set G))
    (hc : Nat.Coprime (Nat.card P) (Nat.card E))
    (m k : ℕ) (hE : Nat.card E = 2 ^ (m+k))
    (hM : Nat.card (⁅E,P⁆ : Subgroup G) = 2 ^ m) :
    Nat.card (E ⊓ centralizer (P : Set G) : Subgroup G) = 2 ^ k := by
  apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ m)
  rw [← pow_add, ← hE, ← hM]
  exact commutator_card_mul_centralizer_card E P hn hc

end Subgroup
