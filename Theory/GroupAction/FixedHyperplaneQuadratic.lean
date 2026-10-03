module

public import Theory.GroupAction.Defs
public import Mathlib.GroupTheory.Index

/-!
# Quadratic actions with a common fixed subgroup of index two

The action preserves its common fixed subgroup and its complement. The
index-two multiplication criterion therefore puts every displacement in the
fixed subgroup, so the second action commutator is trivial. Neither actor
finiteness nor elementary-abelian hypotheses are needed.
-/

@[expose] public section

/-- An action whose common fixed subgroup has index two has fixed displacement. -/
theorem commutatorAction_le_fixedPoints_of_index_two
    {Y V : Type*} [Group Y] [Group V] [MulDistribMulAction Y V]
    (hindex : (FixedPoints.subgroup Y V).index = 2) :
    commutatorAction Y V ≤ FixedPoints.subgroup Y V := by
  apply (Subgroup.closure_le (K := FixedPoints.subgroup Y V)).mpr
  rintro displacement ⟨actor, vector, _, rfl⟩
  apply (Subgroup.mul_mem_iff_of_index_two hindex).mpr
  rw [Subgroup.inv_mem_iff]
  constructor
  · intro hvector
    rw [(FixedPoints.mem_subgroup (M := Y) (α := V) (a := vector)).mp hvector actor]
    exact hvector
  · intro hvector
    have heq := (FixedPoints.mem_subgroup (M := Y) (α := V)
      (a := actor • vector)).mp hvector actor⁻¹
    rw [inv_smul_smul] at heq
    rwa [← heq] at hvector

/-- A common fixed subgroup of index two makes the second commutator trivial. -/
theorem commutatorAction₂_eq_bot_of_fixed_index_two
    {Y V : Type*} [Group Y] [Group V] [MulDistribMulAction Y V]
    (hindex : (FixedPoints.subgroup Y V).index = 2) :
    commutatorAction₂ Y V = ⊥ := by
  apply le_antisymm _ bot_le
  apply (Subgroup.closure_le (K := (⊥ : Subgroup V))).mpr
  rintro displacement ⟨actor, vector, hvector, rfl⟩
  have hfixed := commutatorAction_le_fixedPoints_of_index_two hindex hvector
  rw [(FixedPoints.mem_subgroup (M := Y) (α := V) (a := vector)).mp hfixed actor,
    inv_mul_cancel]
  exact Subgroup.one_mem _

/-- The cardinality form of fixed-hyperplane quadraticity, using the supplied action. -/
theorem fixed_hyperplane_isQuadraticAction
    {Y V : Type*} [Group Y] [Group V] [Finite V] [MulDistribMulAction Y V]
    (hindex : Nat.card V = 2 * Nat.card (FixedPoints.subgroup Y V)) :
    commutatorAction₂ Y V = ⊥ := by
  apply commutatorAction₂_eq_bot_of_fixed_index_two
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos
    ((FixedPoints.subgroup Y V).index_mul_card.trans hindex)
