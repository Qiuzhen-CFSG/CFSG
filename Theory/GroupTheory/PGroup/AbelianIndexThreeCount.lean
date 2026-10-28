module

public import Theory.GroupTheory.PGroup.AbelianIndexThreeStructure
public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.Tactic.Linarith

/-!
# Counting abelian index-three subgroups

A nonabelian finite three-group has at most four abelian index-three subgroups.
If there are two, their intersection is the center, of index nine. Each
abelian index-three subgroup has three times the order of the center, so its
complement of the center has twice that order. These complements are pairwise
disjoint inside the complement of the center, whose order is eight times that
of the center. The family therefore has size at most four. A family with at
most one member is handled separately.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, A.3.21(c),
printed pp.55–56 (`refs/quasithin.pdf`).
-/

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
/-- A nonabelian finite three-group has at most four abelian index-three subgroups. -/
public theorem card_abelian_index_three_le_four (hG : IsPGroup 3 G)
    (hn : ¬ IsMulCommutative G) :
    Nat.card {A : Subgroup G // IsMulCommutative A ∧ A.index = 3} ≤ 4 := by
  classical
  let F := {A : Subgroup G // IsMulCommutative A ∧ A.index = 3}
  change Nat.card F ≤ 4
  by_cases hs : Subsingleton F
  · let : Subsingleton F := hs
    have hle : Nat.card F ≤ 1 := by
      simpa using Nat.card_le_card_of_injective (fun _ : F => ())
        (fun x y _ => Subsingleton.elim x y)
    omega
  · have : Nontrivial F := not_subsingleton_iff_nontrivial.mp hs
    obtain ⟨A, B, hne⟩ := exists_pair_ne F
    have hAB : A.val ≠ B.val := fun h => hne (Subtype.ext h)
    have hz := center_index_eq_nine_of_distinct_abelian_index_three hG hn A.val B.val
      A.property.1 B.property.1 A.property.2 B.property.2 hAB
    let z := Nat.card (center G)
    have hzpos : 0 < z := Nat.card_pos
    have hgz : Nat.card G = 9 * z := by
      have h := (center G).index_mul_card
      rw [hz] at h
      exact h.symm
    have hAz (C : F) : Nat.card C.val = 3 * z := by
      have h := C.val.index_mul_card
      rw [C.property.2, hgz] at h
      omega
    let s : F → Set G := fun C => (C.val : Set G) \ (center G : Set G)
    have hsz (C : F) : (s C).ncard = 2 * z := by
      rw [Set.ncard_sdiff (center_le_of_abelian_index_three hG hn C.val C.property.1 C.property.2)]
      change Nat.card C.val - z = 2 * z
      rw [hAz]
      omega
    have hdis : Pairwise (Function.onFun Disjoint s) := by
      intro C D hCD
      apply Set.disjoint_left.mpr
      intro x hx hy
      have hi := inf_eq_center_of_distinct_abelian_index_three hG hn C.val D.val
        C.property.1 D.property.1 C.property.2 D.property.2
        (fun h => hCD (Subtype.ext h))
      exact hx.2 (hi ▸ (show x ∈ C.val ⊓ D.val from ⟨hx.1, hy.1⟩))
    have hsub : (⋃ C, s C) ⊆ Set.univ \ (center G : Set G) := by
      intro x hx
      obtain ⟨C, hC⟩ := Set.mem_iUnion.mp hx
      exact ⟨Set.mem_univ _, hC.2⟩
    have hcount := Set.ncard_le_ncard hsub
    rw [Set.ncard_iUnion_of_finite (fun C => Set.toFinite (s C)) hdis] at hcount
    let : Fintype F := Fintype.ofFinite F
    simp only [hsz, finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ,
      smul_eq_mul] at hcount
    rw [Set.ncard_sdiff (Set.subset_univ _), Set.ncard_univ] at hcount
    change Fintype.card F * (2 * z) ≤ Nat.card G - z at hcount
    rw [hgz] at hcount
    have hgsub : 9 * z - z = 8 * z := by omega
    rw [hgsub] at hcount
    rw [Nat.card_eq_fintype_card]
    nlinarith
end Subgroup
