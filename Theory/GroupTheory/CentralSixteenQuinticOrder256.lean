module

public import Theory.GroupTheory.CentralSixteenQuinticSplitting
public import Theory.GroupTheory.PGroup.OrderSixteenDerived

/-!
# The trivial quotient action at core order at most 256

A quintic actor fixing no nonidentity point of a central sixteen splits off
that sixteen when it acts trivially on the quotient. The central complement
has order at most sixteen, and hence cyclic derived subgroup. The hypothesis
on the quotient action is retained explicitly; a nontrivial action on a
section of order sixteen remains a separate case.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A central sixteen with fixed-free quintic action and trivial quotient action
has cyclic derived subgroup when the whole two-group has order at most 256. -/
theorem cyclic_derived_of_central_sixteen_quintic_of_card_le_256
    (Q V A : Subgroup G) (hQ : IsPGroup 2 Q)
    (hVQ : V ≤ Q) (hVC : V ≤ centralizer (Q : Set G))
    (hcardV : Nat.card V = 16) (hcardA : Nat.card A = 5)
    (hAQ : A ≤ normalizer (Q : Set G))
    (hcomm : ⁅Q,A⁆ ≤ V) (hfixed : V ⊓ centralizer (A : Set G) = ⊥)
    (hsmall : Nat.card Q ≤ 256) : IsCyclic (⁅Q,Q⁆ : Subgroup G) := by
  let C := Q ⊓ centralizer (A : Set G)
  have hcop : Nat.Coprime (Nat.card A) (Nat.card Q) := by
    obtain ⟨n,hn⟩ := hQ.exists_card_eq
    rw [hcardA,hn]
    exact (by decide : Nat.Coprime 5 2).pow_right n
  have hsplit : V ⊔ C = Q := by
    apply le_antisymm (sup_le hVQ inf_le_left)
    exact (eq_commutator_sup_centralizer_of_solvable_coprime Q A hAQ
      (@IsNilpotent.to_isSolvable Q _ hQ.isNilpotent) hcop).le.trans
        (sup_le_sup hcomm le_rfl)
  have hdis : Disjoint V C := by
    apply disjoint_iff.mpr
    apply bot_unique
    exact (inf_le_inf_left V (show C ≤ centralizer (A : Set G) from inf_le_right)).trans
      hfixed.le
  have hn : C ≤ normalizer (V : Set G) :=
    (le_centralizer_iff.mp (hVC.trans (centralizer_le (show C ≤ Q from inf_le_left)))).trans
      (Subgroup.centralizer_le_normalizer (V : Set G))
  have hc : Nat.card C ≤ 16 := by
    have hh := card_sup_eq_mul_of_normalizes_of_disjoint V C hn hdis
    rw [hsplit,hcardV] at hh
    omega
  let := (hQ.to_le (show C ≤ Q from inf_le_left)).isCyclic_commutator_of_card_le_sixteen hc
  have hcyc : IsCyclic (⁅C,C⁆ : Subgroup G) := by
    have hh := ((_root_.commutator C).equivMapOfInjective C.subtype C.subtype_injective).isCyclic.mp
      (inferInstance : IsCyclic (_root_.commutator C))
    rwa [map_subtype_commutator] at hh
  rw [commutator_eq_of_central_supplement ((sup_comm C V).trans hsplit) hVC]
  exact hcyc

end Subgroup
