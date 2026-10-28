module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiSections
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.ActorLevi

/-!
# The two-sided regular Suzuki parameter restriction

The effective radical argument in (6C) is directional: when the `j` endpoint
is Suzuki, it bounds the literal opposite root exponent.  In a pair of
regular Suzuki endpoints the same argument must be applied in both
orientations.  This module records both inequalities on the same marked
quotient, with the actual canonical roots and right-conjugation actions.  It
does not identify the two Suzuki parameters or claim the later source
exclusion; those are separate (6C)/(6E) obligations.

Source: Fong--Seitz I, (6C), printed pp.39--41.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open scoped MatrixGroups

namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- Applying the genuine Suzuki effective-section bound in both orientations
gives the two inequalities for a regular Suzuki/Suzuki pair.  The hypotheses
`hi` and `hj` are the actual cardinalities of the two canonical simple roots;
they are retained explicitly so this theorem does not replace source roots by
an unrelated order calculation. -/
theorem suzuki_suzuki_parameter_bounds
    (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m n ai aj : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (μj : rankOne Q split j ≃* SuzukiMatrixGroup n)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup n)
    (hi : Nat.card (simpleRoot Q split i) = 2^ai)
    (hj : Nat.card (simpleRoot Q split j) = 2^aj) :
    4*(2*m+1) ≤ 3*aj ∧ 4*(2*n+1) ≤ 3*ai := by
  have hij' := suzuki_hexagon_parameter_bound Q split i hm μi hhex j hij.symm
    (UnitarySource.actorReflection Q split i) hKi νi hj
  have hji := suzuki_hexagon_parameter_bound Q split j hn μj hhex i hij
    (UnitarySource.actorReflection Q split j) hKj νj hi
  exact ⟨hij', hji⟩

/-- In the canonical Suzuki root coordinates the preceding inequalities have
the source exponents `2(2m+1)` and `2(2n+1)`. -/
theorem suzuki_suzuki_canonical_parameter_bounds
    (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (μj : rankOne Q split j ≃* SuzukiMatrixGroup n)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup n) :
    2*(2*m+1) ≤ 3*(2*n+1) ∧ 2*(2*n+1) ≤ 3*(2*m+1) := by
  have hi : Nat.card (simpleRoot Q split i) = 2^(2*(2*m+1)) := by
    rw [Nat.card_congr νi.toEquiv, ReeSource.matrixRoot_card, ← pow_mul]
    congr 1
    omega
  have hj : Nat.card (simpleRoot Q split j) = 2^(2*(2*n+1)) := by
    rw [Nat.card_congr νj.toEquiv, ReeSource.matrixRoot_card, ← pow_mul]
    congr 1
    omega
  obtain ⟨hijm, hnmi⟩ := suzuki_suzuki_parameter_bounds Q split hhex i j
    hij hKi hKj hm hn μi νi μj νj hi hj
  exact ⟨by omega, by omega⟩

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
