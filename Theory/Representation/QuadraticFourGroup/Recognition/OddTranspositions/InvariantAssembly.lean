module

public import Theory.Representation.QuadraticFourGroup.Recognition.OddTranspositions
public import Theory.Representation.QuadraticFourGroup.Recognition.OddTranspositions.DiagonalModel

/-!
# Odd transpositions from the source diagonal structural assertions

This applies invariant maximality inside the actual component orbit to the
linear odd-transposition theorem. The three explicit remaining inputs are
maximality of K Z(E), its normalizer bound, and reverse commutator containment
for `K = E(C_E(a))`. They must still be proved from the norm-diagonal model;
this conditional assembly is not the completed GLS2 Theorem 25.14.

Source: GLS2, Chapter G, Theorem 25.14, Steps 1--3.
-/

public section

open Subgroup Theory.GroupTheory

namespace Representation.QuadraticFourGroup

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L B : Subgroup G} {a : G}

/-- The genuine source structural inputs feed the already proved linear
contradiction, without a maximal-subgroup hypothesis on Y. -/
theorem Hypotheses.hasOddTranspositions_of_invariant_diagonal
    [ρ.IsIrreducible] (h : Hypotheses ρ L B a)
    (hgen : L ⊔ B = ⊤) (hcore : pCore 2 G = ⊥)
    (hmax : IsMaximalInvariantIn (diagonalLayer L B a ⊔ orbitCenter L B)
      (componentOrbit L B) B)
    (hN : normalizer ((diagonalLayer L B a ⊔ orbitCenter L B : Subgroup G) : Set G) ≤
      orbitCenter L B ⊔ diagonalOvergroup L B a)
    (hreverse : diagonalLayer L B a ≤ ⁅diagonalLayer L B a, B⁆) :
    HasOddTranspositions a := by
  apply h.hasOddTranspositions_of_diagonal_generation
    (le_antisymm (h.diagonalLayer_commutator_le hgen) hreverse)
  intro x hx
  apply h.diagonal_generation_of_even_of_invariant_maximality hgen hcore hmax hN
  rw [hx]
  exact ⟨1, rfl⟩

end Representation.QuadraticFourGroup

end
