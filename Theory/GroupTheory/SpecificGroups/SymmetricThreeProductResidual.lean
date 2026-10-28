module

public import Theory.GroupTheory.PResidual.PCoreQuotient
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The residual quotient above a product of two symmetric groups of degree three

The subgroup A₃ × A₃ has order nine and index four in S₃ × S₃. Its odd
order puts it in the two-residual, and its two-group quotient proves the
reverse containment. Its two-core is trivial. Consequently any finite group
surjecting onto S₃ × S₃ with two-group kernel has residual core quotient
of order nine.

Application: the invariant Held local used in Aschbacher--Smith, printed
p.526, with local model data from GLS3 Table 5.3p.
-/

public section
namespace SymmetricThreeProductResidual
open Subgroup

private theorem three_card : Nat.card (alternatingGroup (Fin 3)) = 3 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  rfl

private theorem nine_card :
    Nat.card ((alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3))) = 9 := by
  rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, three_card]

/-- The two-residual is the literal product of alternating subgroups. -/
theorem residual_eq : pResidual 2 (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) =
    (alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3)) := by
  apply le_antisymm
  · apply sInf_le
    refine ⟨inferInstance, IsPGroup.of_card (n := 2) ?_⟩
    change ((alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3))).index = 2 ^ 2
    simp [Subgroup.index_prod]
  · intro x hx
    let y : (alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3)) := ⟨x, hx⟩
    have hy : y ^ 9 = 1 := nine_card ▸ pow_card_eq_one' (x := y)
    have hx9 : x ^ 9 = 1 := congrArg Subtype.val hy
    exact mem_pResidual_of_orderOf_coprime
      ((by decide : Nat.Coprime 2 9).of_dvd_right (orderOf_dvd_of_pow_eq_one hx9))

theorem residual_card : Nat.card (pResidual 2 (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) = 9 := by
  rw [residual_eq]
  exact nine_card

theorem residual_core_eq_bot : pCore 2 (pResidual 2 (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) = ⊥ := by
  apply Subgroup.card_eq_one.mp
  rcases (pCore_isPGroup (p := 2) (G := pResidual 2 (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))).card_eq_or_dvd with h | h
  · exact h
  · have hd := h.trans (pCore 2 (pResidual 2 (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))).card_subgroup_dvd_card
    rw [residual_card] at hd
    norm_num at hd

theorem residual_core_quotient_card :
    Nat.card (pResidual 2 (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) ⧸ pCore 2 (pResidual 2 (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) = 9 := by
  rw [residual_core_eq_bot, Nat.card_congr QuotientGroup.quotientBot.toEquiv]
  exact residual_card

/-- Only a genuine surjection and a two-group kernel are required of the model map. -/
theorem residual_core_quotient_card_of_surjective
    {G : Type*} [Group G] [Finite G] (f : G →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) :
    Nat.card (pResidual 2 G ⧸ pCore 2 (pResidual 2 G)) = 9 := by
  rw [Nat.card_congr (f.pResidualCoreQuotientEquiv hf hk).toEquiv]
  exact residual_core_quotient_card

end SymmetricThreeProductResidual
