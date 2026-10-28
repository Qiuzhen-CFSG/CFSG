module
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

/-!
# Relative centralizer index from a two-coset layer

Let A, U, Z and C be subgroups of a finite group. Suppose A centralizes
Z and C, U∩Z has index two in U, and [A,U] lies in C. Then the index
of C_A(U) in A is at most |C|. The central layer Z and the commutator
target C are deliberately separate.

Choose u in U outside Z. Centrality of the commutator values makes
 a ↦ [u,a] a homomorphism from A to C. Its kernel is C_A(U), since
u and U∩Z generate U. Counting the image proves the bound.

This is the relative centralizer count in Stellmacher (10.1)(a3), printed
p.61 before (8), where Z is the neighboring central plane while C is the
first central line. Source: `refs/files/stellmacher-n-group.pdf`.
-/

namespace Subgroup
open scoped commutatorElement

public theorem relIndex_centralizer_le_card_of_central_index_two_layer
    {G : Type*} [Group G] [Finite G] (A U Z C : Subgroup G)
    (hZA : A ≤ centralizer (Z : Set G)) (hCA : A ≤ centralizer (C : Set G))
    (hindex : (Z.subgroupOf U).index = 2) (hcomm : ⁅A,U⁆ ≤ C) :
    (centralizer (U : Set G)).relIndex A ≤ Nat.card C := by
  classical
  have hnot : ¬ U ≤ Z := by
    intro hle
    have heq : Z.subgroupOf U = ⊤ := subgroupOf_eq_top.mpr hle
    rw [heq,index_top] at hindex
    contradiction
  obtain ⟨u,hu,huZ⟩ := SetLike.not_le_iff_exists.mp hnot
  have hvalue (a : A) : ⁅u,(a:G)⁆ ∈ C := by
    apply hcomm
    rw [commutator_comm]
    exact commutator_mem_commutator hu a.property
  let displacement : A →* C := {
    toFun := fun a => ⟨⁅u,(a:G)⁆,hvalue a⟩
    map_one' := Subtype.ext (by simp)
    map_mul' := by
      intro a b
      apply Subtype.ext
      change ⁅u,(a:G)*(b:G)⁆ = ⁅u,(a:G)⁆*⁅u,(b:G)⁆
      rw [commutatorElement_mul_right_eq_mul_conj]
      have hc := mem_centralizer_iff.mp (hCA a.property) _ (hvalue b)
      calc
        _ = ⁅u,(a:G)⁆*((a:G)*⁅u,(b:G)⁆)*(a:G)⁻¹ := by group
        _ = _ := by rw [← hc]; group }
  have hker : displacement.ker = (centralizer (U : Set G)).subgroupOf A := by
    apply le_antisymm
    · intro a ha
      have hua : Commute u (a:G) := commutatorElement_eq_one_iff_commute.mp
        (congrArg Subtype.val (MonoidHom.mem_ker.mp ha))
      change (a:G) ∈ centralizer (U : Set G)
      rw [mem_centralizer_iff]
      intro w hw
      by_cases hwZ : w∈Z
      · exact mem_centralizer_iff.mp (hZA a.property) w hwZ
      have hprod : u⁻¹*w∈Z := by
        have hh : (⟨u,hu⟩:U)⁻¹*⟨w,hw⟩ ∈ Z.subgroupOf U := by
          rw [mul_mem_iff_of_index_two hindex]
          change u⁻¹∈Z ↔ w∈Z
          simp [huZ,hwZ]
        exact hh
      have hz : Commute (u⁻¹*w) (a:G) :=
        mem_centralizer_iff.mp (hZA a.property) _ hprod
      simpa only [mul_inv_cancel_left] using (hua.mul_left hz).eq
    · intro a ha
      apply MonoidHom.mem_ker.mpr
      apply Subtype.ext
      exact commutatorElement_eq_one_iff_commute.mpr
        (mem_centralizer_iff.mp ha u hu)
  change ((centralizer (U : Set G)).subgroupOf A).index ≤ Nat.card C
  rw [← hker,index_ker]
  exact Nat.card_le_card_of_injective displacement.range.subtype Subtype.val_injective

end Subgroup
