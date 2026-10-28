module

public import Theory.GroupAction.Defs
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.PGroup

/-!+# The direct-sum obstruction in A.1.17

The printed direct-sum assertion of Aschbacher–Smith A.1.17, p.24, cannot
hold for all abelian r-group actors. Let C4 act on C3 by inversion through
its quotient C2. The action commutators generate C3, but both the trivial
subgroup and the order-two subgroup of C4 fix all of C3. Both have cyclic
quotient and nontrivial fixed subgroup. Thus two distinct members of the
printed indexing family have nondisjoint fixed subgroups.

This certificate records the source obstruction without altering the valid
generation assertion or silently adding an elementary-abelian hypothesis.
-/

namespace CFSG.Quasithin.ChapterA

private abbrev Actor := Multiplicative (ZMod 4)
private abbrev Target := Multiplicative (ZMod 3)

private def inversionAction (a : Actor) (x : Target) : Target :=
  if a.toAdd.val % 2 = 0 then x else x⁻¹

private instance inversionMulAction : MulDistribMulAction Actor Target where
  smul := inversionAction
  one_smul := by decide
  mul_smul := by decide
  smul_mul := by decide
  smul_one := by decide

private def evenSubgroup : Subgroup Actor where
  carrier := {a | a.toAdd.val % 2 = 0}
  one_mem' := by decide
  mul_mem' := by decide
  inv_mem' := by decide

private theorem evenSubgroup_ne_bot : evenSubgroup ≠ ⊥ := by
  intro h
  have hm : Multiplicative.ofAdd (2 : ZMod 4) ∈ evenSubgroup := by
    change (2 : ZMod 4).val % 2 = 0
    decide
  rw [h, Subgroup.mem_bot] at hm
  exact (by decide : Multiplicative.ofAdd (2 : ZMod 4) ≠ (1 : Actor)) hm

private theorem evenSubgroup_fixed : fixedPointSubgroup evenSubgroup Target = ⊤ := by
  apply top_unique
  intro x _ a
  change inversionAction a.val x = x
  have ha : a.val.toAdd.val % 2 = 0 := a.property
  simp only [inversionAction, ha, ite_true]

private theorem inversion_commutators : commutatorAction Actor Target = ⊤ := by
  apply top_unique
  intro x _
  apply Subgroup.subset_closure
  refine ⟨Multiplicative.ofAdd (1 : ZMod 4), x, Subgroup.mem_top _, ?_⟩
  exact (by decide : ∀ x : Target,
    x = x⁻¹ * inversionAction (Multiplicative.ofAdd (1 : ZMod 4)) x) x

/-- A concrete action satisfying A.1.17 has distinct eligible actor subgroups
whose nontrivial fixed groups are not disjoint. Hence the printed internal
direct-sum assertion needs an additional hypothesis or a different family. -/
public theorem lemma_A_1_17_directSum_obstruction :
    ∃ action : MulDistribMulAction (Multiplicative (ZMod 4)) (Multiplicative (ZMod 3)),
      letI := action
      IsPGroup 2 (Multiplicative (ZMod 4)) ∧
      Nat.Coprime 2 (Nat.card (Multiplicative (ZMod 3))) ∧
      commutatorAction (Multiplicative (ZMod 4)) (Multiplicative (ZMod 3)) = ⊤ ∧
      ∃ B C : Subgroup (Multiplicative (ZMod 4)), B ≠ C ∧
        IsCyclic ((Multiplicative (ZMod 4)) ⧸ B) ∧
        IsCyclic ((Multiplicative (ZMod 4)) ⧸ C) ∧
        fixedPointSubgroup B (Multiplicative (ZMod 3)) ≠ ⊥ ∧
        fixedPointSubgroup C (Multiplicative (ZMod 3)) ≠ ⊥ ∧
        ¬ Disjoint (fixedPointSubgroup B (Multiplicative (ZMod 3)))
          (fixedPointSubgroup C (Multiplicative (ZMod 3))) := by
  refine ⟨inversionMulAction, ?_, ?_, inversion_commutators,
    ⊥, evenSubgroup, Ne.symm evenSubgroup_ne_bot, ?_, ?_, ?_, ?_, ?_⟩
  · apply IsPGroup.of_card (n := 2)
    simp [Nat.card_eq_fintype_card]
  · rw [Nat.card_eq_fintype_card]
    decide
  · exact isCyclic_of_surjective (QuotientGroup.mk' ⊥) (QuotientGroup.mk'_surjective ⊥)
  · exact isCyclic_of_surjective (QuotientGroup.mk' evenSubgroup)
      (QuotientGroup.mk'_surjective evenSubgroup)
  all_goals
    have hbot : fixedPointSubgroup (⊥ : Subgroup Actor) Target = ⊤ := by
      apply top_unique
      intro x _ a
      have ha : (a : Actor) = 1 := a.property
      change inversionAction a.val x = x
      rw [ha]
      rfl
    try rw [evenSubgroup_fixed]
    try rw [hbot]
    simp

end CFSG.Quasithin.ChapterA
