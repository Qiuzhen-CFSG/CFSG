module

public import Theory.GroupAction.SemilinearPointStabilizerExceptional.PrimeReduction.Basic
public import Theory.GroupAction.SemilinearPointStabilizerExceptional.PrimeReduction.TwoGroupExclusion.Solvability

/-!
# The coefficient stabilizer is not a two-group

The scalar subgroup K is cyclic of order |F| - 1, and orbit–stabilizer gives
its index as |F| |Γ| for the literal two-point stabilizer Γ. If Γ were a
two-group, K would have two-power index, forcing X to be solvable by the
abelian prime-power-index theorem. The original trivial-two-core hypothesis
already rules out solvability. No scalar normal-generation hypothesis is used.

Source: GLS, Volume 4, Chapter 1, Lemma 3.8(b),
`refs/KGroup/GLS4/Chapter1.tex`, lines 419–430.
-/

public section

namespace MulAction.SemilinearPointStabilizer.Coordinates

variable {X F : Type*} [Group X] [Finite X] [Field F] [Finite F]
    [MulAction X F] [FaithfulSMul X F] (c : Coordinates X F)

include c

/-- The scalar subgroup's index, computed with the actual two-point stabilizer. -/
theorem scalarSubgroup_index [IsPretransitive X F] :
    c.scalarSubgroup.index = Nat.card F * Nat.card (twoPoint (X := X) (F := F)) := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := c.scalarSubgroup))
  rw [c.scalarSubgroup.card_mul_index, c.card_group, c.card_scalarSubgroup]
  ring

/-- GLS 4, Lemma 3.8(b), under the original action and two-core hypotheses. -/
theorem not_isPGroup_twoPoint {n : ℕ} (hn : 2 ≤ n)
    (htwo : IsMultiplyPretransitive X F 2) (hF : Nat.card F = 2 ^ n)
    (hcore : pCore 2 X = ⊥) :
    ¬ IsPGroup 2 (twoPoint (X := X) (F := F)) := by
  intro hΓ
  let : IsMultiplyPretransitive X F 2 := htwo
  let : IsPretransitive X F := isPretransitive_of_is_two_pretransitive
  let : IsCyclic c.scalarSubgroup := c.scalarSubgroup_isCyclic
  obtain ⟨k, hk⟩ := hΓ.exists_card_eq
  have hindex : c.scalarSubgroup.index = 2 ^ (n + k) := by
    rw [c.scalarSubgroup_index, hF, hk, pow_add]
  exact c.not_isSolvable hn htwo hF hcore
    (c.scalarSubgroup.isSolvable_of_isMulCommutative_of_prime_power_index Nat.prime_two hindex)

end MulAction.SemilinearPointStabilizer.Coordinates
