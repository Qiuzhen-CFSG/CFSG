module
public import Theory.GroupTheory.SymmetricThreeTwoCore
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum

/-!
# Normal subgroups inside a proper S₃ subgroup containing an involution

A proper subgroup containing an involution has order two. Any normal subgroup
it contains therefore lies in the trivial two-core of S₃. The statement is
transported through an actual group equivalence.

Source application: Aschbacher--Smith 14.3.25, printed p.1001. The central
module kernel preserves the marked plane in the original S₃ action image.
-/

public section
open Subgroup
namespace SymmetricThree
variable {D : Type*} [Group D] [Finite D]

/-- A proper subgroup of S3 containing an involution contains no nontrivial normal subgroup. -/
theorem normal_eq_bot_of_le_proper_with_involution (e : D ≃* Equiv.Perm (Fin 3))
    (P N : Subgroup D) [N.Normal] (hP : P ≠ ⊤)
    (a : D) (ha : a ∈ P) (ha2 : orderOf a = 2) (hNP : N ≤ P) : N = ⊥ := by
  have hD : Nat.card D = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  have hdiv := P.card_subgroup_dvd_card
  rw [hD] at hdiv
  have htwo : 2 ∣ Nat.card P := ha2 ▸ P.orderOf_dvd_natCard ha
  have hp : Nat.card P = 2 := by
    have hlt : Nat.card P < 6 := by
      rw [← hD]
      apply lt_of_le_of_ne P.card_le_card_group
      intro he
      apply hP
      apply top_unique
      intro x _
      obtain ⟨y,rfl⟩ := (P.subtype_injective.bijective_of_nat_card_le he.symm.le).surjective x
      exact y.property
    have hn := Nat.card_pos (α := P)
    interval_cases hcard : Nat.card P <;> norm_num at *
  have hpg : IsPGroup 2 P := IsPGroup.of_card (n := 1) (by simpa using hp)
  have hn : IsPGroup 2 N := hpg.to_le hNP
  have hc : N ≤ pCore 2 D := le_sSup ⟨inferInstance,hn⟩
  have hker := ker_eq_twoCore_of_surjective_perm_three e.toMonoidHom e.surjective (by
    rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective]
    exact IsPGroup.of_subsingleton 2 _)
  rw [← hker,e.toMonoidHom.ker_eq_bot_iff.mpr e.injective] at hc
  exact le_bot_iff.mp hc
end SymmetricThree
