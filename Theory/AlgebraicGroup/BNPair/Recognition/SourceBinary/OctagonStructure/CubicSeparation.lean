module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.CubicAbelian

/-!
# The subgroup join forced by the cubic fixed product

The cubic Cartan calculation identifies the fixed part of the seven-root
radical with a literal product of three root subgroups.  This extension records
the subgroup consequence used by the Fong--Seitz (6G) separation argument:
the fixed radical is the join of exactly those three root groups.  The proof is
purely set-theoretic and keeps the marked quotient and all root maps visible.
-/

public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem three_product_sup {Y : Type*} [Group Y] (A B C K : Subgroup Y)
    (hp : (K : Set Y) = (A : Set Y) * (B : Set Y) * (C : Set Y)) :
    A ⊔ B ⊔ C = K := by
  have hA : A ≤ K := by
    intro a ha
    change a ∈ (K : Set Y)
    rw [hp]
    exact ⟨a, ⟨a, ha, 1, one_mem _, mul_one _⟩, 1, one_mem _, mul_one _⟩
  have hB : B ≤ K := by
    intro b hb
    change b ∈ (K : Set Y)
    rw [hp]
    exact ⟨b, ⟨1, one_mem _, b, hb, one_mul _⟩, 1, one_mem _, mul_one _⟩
  have hC : C ≤ K := by
    intro c hc
    change c ∈ (K : Set Y)
    rw [hp]
    exact ⟨1, ⟨1, one_mem _, 1, one_mem _, one_mul _⟩, c, hc, one_mul _⟩
  apply le_antisymm (sup_le (sup_le hA hB) hC)
  intro x hx
  change x ∈ (K : Set Y) at hx
  obtain ⟨ab, ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩ := hp ▸ hx
  exact mul_mem_sup (mul_mem_sup ha hb) hc

/-- The cubic Cartan fixed radical is the join of its three fixed roots. -/
theorem separated_radical_centralizer_sup (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)))
    (hc : ∀ w : Weyl Q,
      (c : X ⧸ Q.D) ∈ centralizer (rootAt Q split i w : Set (X ⧸ Q.D)) ∧
      rootAt Q split j w ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) = ⊥) :
    rootAt Q split i (Q.simple j) ⊔
        rootAt Q split i (Q.simple j * Q.simple i * Q.simple j) ⊔
        rootAt Q split i (Q.simple j * Q.simple i) =
      simpleRemainder Q split i ⊓
        centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) := by
  apply three_product_sup
  exact separated_radical_centralizer_product Q split hm i j hij c hc

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
