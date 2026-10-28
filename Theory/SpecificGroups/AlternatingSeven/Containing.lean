module
public import Theory.AtlasPort.OtherSporadic.GroupTheory.SmallIndexSimple
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Overgroups of an order-168 subgroup in A₇

The subgroup has index fifteen. Every proper intermediate overgroup would
have index three or five; the faithful coset action of the simple A₇ would
then contradict the order of the corresponding symmetric group.

The Chapter 12 rigidity catalogue applies this to the image of the original
hyperplane residual, retaining its inclusion in the same A₇ action quotient.
Source: Aschbacher–Smith, original 12.2.25, printed p.805.
-/

public noncomputable section
open Subgroup
namespace AlternatingSeven.Containing
/-- A subgroup of order 168 in A7 has no proper intermediate overgroup. -/
theorem eq_or_top_of_card (B K : Subgroup (alternatingGroup (Fin 7)))
    (hc : Nat.card B = 168) (hle : B ≤ K) : K = B ∨ K = ⊤ := by
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  have hi : B.index = 15 := by
    have hh := B.card_mul_index
    rw [hc,nat_card_alternatingGroup,Nat.card_fin] at hh
    norm_num [Nat.factorial] at hh
    omega
  have hd : K.index ∣ 15 := hi ▸ index_dvd_of_le hle
  have hcases : K.index = 1 ∨ K.index = 3 ∨ K.index = 5 ∨ K.index = 15 := by
    exact (by decide : ∀ k : Fin 16, k.val ∣ 15 → k.val = 1 ∨ k.val = 3 ∨ k.val = 5 ∨ k.val = 15)
      ⟨K.index,Nat.lt_succ_of_le (Nat.le_of_dvd (by decide : 0 < 15) hd)⟩ hd
  rcases hcases with h1 | h3 | h5 | h15
  · exact Or.inr (index_eq_one.mp h1)
  · exact Or.inr (Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt K (by
      rw [h3,nat_card_alternatingGroup,Nat.card_fin]; norm_num [Nat.factorial]))
  · exact Or.inr (Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt K (by
      rw [h5,nat_card_alternatingGroup,Nat.card_fin]; norm_num [Nat.factorial]))
  · apply Or.inl
    apply Eq.symm
    apply eq_of_le_of_card_ge hle
    have hh := K.card_mul_index
    rw [h15,nat_card_alternatingGroup,Nat.card_fin] at hh
    norm_num [Nat.factorial] at hh
    omega
end AlternatingSeven.Containing
