module

public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The two-residual of a symmetric group

The alternating subgroup has two-group quotient. Conversely it is generated
by three-cycles, and every odd-order element belongs to the two-residual.
Thus O²(Sym(α)) is the actual alternating subgroup.

Application: the local A₅ image in Aschbacher–Smith, proof of Lemma 16.4.7,
printed p.1187.
-/

open Subgroup

/-- The two-residual of the symmetric group is its alternating subgroup. -/
public theorem Equiv.Perm.twoResidual_eq_alternating (α : Type*)
    [Fintype α] [DecidableEq α] [Nontrivial α] :
    pResidual 2 (Equiv.Perm α) = alternatingGroup α := by
  apply le_antisymm
  · apply sInf_le
    refine ⟨inferInstance, IsPGroup.of_card (n := 1) ?_⟩
    change (alternatingGroup α).index = 2 ^ 1
    simp [alternatingGroup.index_eq_two]
  · rw [← Equiv.Perm.closure_three_cycles_eq_alternating]
    rw [Subgroup.closure_le]
    intro a ha
    exact mem_pResidual_of_orderOf_coprime (by rw [ha.orderOf]; decide)
