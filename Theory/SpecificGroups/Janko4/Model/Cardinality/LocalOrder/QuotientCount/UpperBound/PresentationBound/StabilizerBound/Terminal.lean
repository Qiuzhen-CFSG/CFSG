module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.PresentationBound.StabilizerBound.Data
public import Mathlib.GroupTheory.OrderOfElement

/-!
# The terminal cyclic subgroup

The final child has one generator, the third generator of the three-generator
presentation. Its cube is a defining relator. The equivalence between its
integer powers and `Fin (orderOf x)` proves finiteness and the bound three,
without assuming the order of any permutation image.
-/

public section
namespace Janko4.Cardinality.QuotientCount.UpperBound.PresentationBound.StabilizerChain
open Subgroup.CosetWordCertificate

theorem level5Generator_cube : (level5Generator 0) ^ 3 = 1 := by
  have h := level5_relator 2
  change eval PresentedGroup.of [(2, true), (2, true), (2, true)] = 1 at h
  change (eval (PresentedGroup.of : Fin 3 → Level5) [(2, true)]) ^ 3 = 1
  simpa [eval_cons, pow_succ, mul_assoc] using h

theorem level5Subgroup_eq_zpowers : level5Subgroup = Subgroup.zpowers (level5Generator 0) := by
  have hr : Set.range level5Generator = {level5Generator 0} := by
    ext x
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      exact congrArg level5Generator (Subsingleton.elim i 0)
    · rintro rfl
      exact ⟨0, rfl⟩
  unfold level5Subgroup
  rw [hr, Subgroup.zpowers_eq_closure]

theorem terminal_bound :
    Finite level5Subgroup ∧ Nat.card level5Subgroup ≤ 3 := by
  rw [level5Subgroup_eq_zpowers]
  have hpow := level5Generator_cube
  have ho : IsOfFinOrder (level5Generator 0) :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by decide, hpow⟩
  refine ⟨Finite.of_equiv _ (finEquivZPowers ho), ?_⟩
  rw [← Nat.card_congr (finEquivZPowers ho), Nat.card_fin]
  exact orderOf_le_of_pow_eq_one (by decide) hpow
end Janko4.Cardinality.QuotientCount.UpperBound.PresentationBound.StabilizerChain
