module

public import Theory.AlgebraicGroup.RootSubgroups.Defs

universe u

/-!
Opposition for positive systems of actual torus roots.

Complete root addition lets us negate a root sum by negating its character
equation. Consequently the negative of a positive system is again positive.
The partition into positive and negative roots also shows that inclusion
between positive systems is equality. These are the root combinatorics used
in the opposite-Borel construction of GLS3, Theorem 1.11.2, and Borel,
*Linear Algebraic Groups*, §§13.18 and 14.1.
-/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]
variable {G : Variety k} [AlgebraicGroup G] {T : ClosedSubgroup G}
variable {D : RootGroupData G T}

/-- Actual root addition commutes with simultaneous negation. -/
public theorem RootGroupData.IsRealization.add_neg_of_add
    (hD : D.IsRealization) (hadd : D.IsRootAdditionComplete)
    {a b c : D.Root} (hab : D.add a b = some c) :
    D.add (D.neg a) (D.neg b) = some (D.neg c) := by
  rcases hD with ⟨_, _, _, hneg, hsum, _⟩
  apply hadd
  rw [hneg, hneg, hneg, hsum a b c hab, mul_inv]

/-- Negating a positive system gives another positive system. The converse
root-addition clause is needed to transport closure under root sums. -/
public theorem IsPositiveSystem.neg_preimage
    {P : Set D.Root} (hP : IsPositiveSystem D P)
    (hD : D.IsRealization) (hadd : D.IsRootAdditionComplete) :
    IsPositiveSystem D (D.neg ⁻¹' P) := by
  refine ⟨?_, ?_, ?_⟩
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro a ha
    have hmem : D.neg a ∈ P ∩ D.neg ⁻¹' P := ha
    rw [hP.1] at hmem
    exact hmem
  · apply Set.eq_univ_iff_forall.mpr
    intro a
    have hmem : D.neg a ∈ P ∪ D.neg ⁻¹' P := by
      rw [hP.2.1]
      exact Set.mem_univ _
    exact hmem
  · intro a ha b hb c hab
    exact hP.2.2 (D.neg a) ha (D.neg b) hb (D.neg c)
      (hD.add_neg_of_add hadd hab)

/-- Two positive systems cannot properly contain one another. -/
public theorem IsPositiveSystem.eq_of_subset
    {P Q : Set D.Root} (hP : IsPositiveSystem D P)
    (hQ : IsPositiveSystem D Q) (hPQ : P ⊆ Q) : P = Q := by
  apply Set.Subset.antisymm hPQ
  intro a haQ
  have hmem : a ∈ P ∪ D.neg ⁻¹' P := by
    rw [hP.2.1]
    exact Set.mem_univ _
  rcases hmem with haP | hnegP
  · exact haP
  · have hbad : a ∈ Q ∩ D.neg ⁻¹' Q := ⟨haQ, hPQ hnegP⟩
    rw [hQ.1] at hbad
    exact hbad.elim

end Theory.AlgebraicGroup
