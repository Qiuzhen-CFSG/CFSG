module

public import Theory.GroupAction.SimpleCosets
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.IsPerfect

/-!
# Orders of the small permutation images of M₂₂ Sylow overgroups

A subgroup of A₆ or S₅ whose order is divisible by eight, with a relatively
normal solvable subgroup of order divisible by three, has order 24. The whole
group is excluded by its nonabelian simple alternating subgroup. For A₆,
simplicity and the faithful coset action also exclude indices three and five.
Only integer divisors are enumerated; no subgroup table is assumed.

These are the quotient order reductions for Aschbacher–Smith 13.8.21(2),
printed p.956 (PDF p.973). Lifting them through the actual M₂₂ restriction maps
is a separate step.
-/

public section

open Subgroup
namespace Sporadic.Mathieu.M22SolvableSylow.LocalClassification

private theorem a6_card : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

private theorem a6_not_solvable : ¬ Group.IsSolvable (alternatingGroup (Fin 6)) := by
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  exact Group.IsPerfect.not_isSolvable _

/-- The six-point alternating image has order 24. -/
theorem a6_card_of_seed (X D : Subgroup (alternatingGroup (Fin 6)))
    (hDX : D ≤ X) (hN : (D.subgroupOf X).Normal) (hsol : Group.IsSolvable D)
    (h3 : 3 ∣ Nat.card D) (h8 : 8 ∣ Nat.card X) : Nat.card X = 24 := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hproper : X ≠ ⊤ := by
    intro he
    have hnormal : D.Normal := by
      constructor
      intro d hd g
      exact (normal_subgroupOf_iff hDX).mp hN d g hd (he ▸ mem_top g)
    rcases hnormal.eq_bot_or_eq_top with hbot | htop
    · rw [hbot, card_bot] at h3
      norm_num at h3
    · apply a6_not_solvable
      let := hsol
      exact Group.isSolvable_of_surjective (f := D.subtype)
        (by rw [htop]; exact topEquiv.surjective)
  have hdiv : Nat.card X ∣ 360 := a6_card ▸ X.card_subgroup_dvd_card
  have h3X : 3 ∣ Nat.card X := h3.trans (card_dvd_of_le hDX)
  have hc : ∀ n ∈ (360 : ℕ).divisors, 8 ∣ n → 3 ∣ n →
      n = 24 ∨ n = 72 ∨ n = 120 ∨ n = 360 := by decide +kernel
  rcases hc _ (Nat.mem_divisors.mpr ⟨hdiv, by decide⟩) h8 h3X with h | h | h | h
  · exact h
  · have hi : X.index = 5 := by
      have hm := X.card_mul_index
      rw [h, a6_card] at hm
      omega
    have hd := X.card_dvd_factorial_index_of_simple hproper
    rw [a6_card, hi] at hd
    norm_num [Nat.factorial] at hd
  · have hi : X.index = 3 := by
      have hm := X.card_mul_index
      rw [h, a6_card] at hm
      omega
    have hd := X.card_dvd_factorial_index_of_simple hproper
    rw [a6_card, hi] at hd
    norm_num [Nat.factorial] at hd
  · exact (hproper (X.eq_top_of_card_eq (h.trans a6_card.symm))).elim

private theorem s5_card : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
  rw [Nat.card_perm, Nat.card_fin]
  decide

/-- The five-point symmetric image has order 24. -/
theorem s5_card_of_seed (X D : Subgroup (Equiv.Perm (Fin 5)))
    (hDX : D ≤ X) (hN : (D.subgroupOf X).Normal) (hsol : Group.IsSolvable D)
    (h3 : 3 ∣ Nat.card D) (h8 : 8 ∣ Nat.card X) : Nat.card X = 24 := by
  have hproper : X ≠ ⊤ := by
    intro he
    have hnormal : D.Normal := by
      constructor
      intro d hd g
      exact (normal_subgroupOf_iff hDX).mp hN d g hd (he ▸ mem_top g)
    let := hnormal
    have hnt : Nontrivial D := (nontrivial_iff_ne_bot D).mpr (by
      intro hbot
      rw [hbot, card_bot] at h3
      norm_num at h3)
    have hA : alternatingGroup (Fin 5) ≤ D :=
      Equiv.Perm.alternatingGroup_le_of_normal (by simp) hnt
    let := hsol
    have : Group.IsSolvable (alternatingGroup (Fin 5)) :=
      Group.isSolvable_of_isSolvable_injective (f := inclusion hA) (inclusion_injective hA)
    let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5)) inferInstance
  have hdiv : Nat.card X ∣ 120 := s5_card ▸ X.card_subgroup_dvd_card
  have h3X : 3 ∣ Nat.card X := h3.trans (card_dvd_of_le hDX)
  have hc : ∀ n ∈ (120 : ℕ).divisors, 8 ∣ n → 3 ∣ n → n = 24 ∨ n = 120 := by
    decide +kernel
  rcases hc _ (Nat.mem_divisors.mpr ⟨hdiv, by decide⟩) h8 h3X with h | h
  · exact h
  · exact (hproper (X.eq_top_of_card_eq (h.trans s5_card.symm))).elim

end Sporadic.Mathieu.M22SolvableSylow.LocalClassification
