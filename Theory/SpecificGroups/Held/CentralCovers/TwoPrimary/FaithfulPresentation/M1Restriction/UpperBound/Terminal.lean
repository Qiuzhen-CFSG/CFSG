module

public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.UpperBound.Data
public import Mathlib.GroupTheory.OrderOfElement

/-!
# The terminal cyclic subgroup

The final child has one generator, the fourth generator of the six-generator
presentation. Its square is a defining relator. The equivalence between its
integer powers and `Fin (orderOf x)` proves finiteness and the bound two,
without assuming the order of any permutation image.
-/

public section
namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.UpperBoundChain
open Subgroup.CosetWordCertificate

theorem level2Generator_square : (level2Generator 0) ^ 2 = 1 := by
  have h := level2_relator 0
  change eval PresentedGroup.of [(3, true), (3, true)] = 1 at h
  change (eval (PresentedGroup.of : Fin 6 → Level2) [(3, true)]) ^ 2 = 1
  simpa [eval_cons, pow_succ, mul_assoc] using h

theorem level2Subgroup_eq_zpowers : level2Subgroup = Subgroup.zpowers (level2Generator 0) := by
  have hr : Set.range level2Generator = {level2Generator 0} := by
    ext x
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      exact congrArg level2Generator (Subsingleton.elim i 0)
    · rintro rfl
      exact ⟨0, rfl⟩
  unfold level2Subgroup
  rw [hr, Subgroup.zpowers_eq_closure]

theorem terminal_bound :
    Finite level2Subgroup ∧ Nat.card level2Subgroup ≤ 2 := by
  rw [level2Subgroup_eq_zpowers]
  have hpow := level2Generator_square
  have ho : IsOfFinOrder (level2Generator 0) :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, hpow⟩
  refine ⟨Finite.of_equiv _ (finEquivZPowers ho), ?_⟩
  rw [← Nat.card_congr (finEquivZPowers ho), Nat.card_fin]
  exact orderOf_le_of_pow_eq_one (by decide) hpow
end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.UpperBoundChain
