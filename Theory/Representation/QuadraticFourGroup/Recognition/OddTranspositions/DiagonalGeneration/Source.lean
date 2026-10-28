module

public import Theory.Representation.QuadraticFourGroup.Models
public import Theory.Representation.QuadraticFourGroup.Recognition.ComponentSpectrum
public import Theory.Representation.QuadraticFourGroup.Recognition.OddTranspositions.Definitions
public import Theory.Representation.QuadraticFourGroup.Recognition.OddTranspositions.DiagonalAssembly

/-!
# Source diagonal generation for involution products

This is the completed structural interface for the odd-transposition argument.
The imported `diagonalLayer_eq_normDiagonal` identifies the intrinsic layer
`K = E(C_E(a))` with the actual component norms. The pair coordinates on
`E/Z(E)` give B-invariant maximality and normalizer control; perfectness then
gives generation by `Y = KB` and `Yˣ` outside `Z(E)Y`. The actual orbit centre
has odd order when `O₂(G) = 1`, so an even-order product `aaˣ` lies outside
that exception.

The theorem below specializes that generation result to the exact premise
of `Hypotheses.hasOddTranspositions_of_diagonal_generation`. Its other
premise is the imported, unconditional `Hypotheses.diagonalLayer_commutator`.
Neither diagonal structure nor maximality remains an additional assumption.

Source: GLS2, Chapter G, Theorem 25.14, Steps 2--3; Chapter B, Lemma 3.25
and the norm construction in the proof of Lemma 3.27. Only the latter's
diagonal construction is used, not its additional centre conclusions under
`O₂′(G) = 1`. The relative centralizer, its layer, and the quotient by the
intrinsic centre retain the definitions in `OddTranspositions.Definitions`.
-/

public section

open Subgroup Theory.GroupTheory

namespace Representation.QuadraticFourGroup

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L B : Subgroup G} {a : G}

/-- The exact generation input of the linear odd-transposition assembly,
with the diagonal structure and the exceptional-subgroup exclusion proved.
Irreducibility is needed only by that subsequent linear assembly. -/
theorem Hypotheses.diagonal_generation_of_order_two
    (h : Hypotheses ρ L B a) (hgen : L ⊔ B = ⊤) (hcore : pCore 2 G = ⊥)
    {x : G} (hx : orderOf (a * (x⁻¹ * a * x)) = 2) :
    diagonalOvergroup L B a ⊔
      (diagonalOvergroup L B a).map (MulAut.conj x⁻¹).toMonoidHom = ⊤ := by
  apply h.diagonal_generation_of_even hgen hcore
  rw [hx]
  exact ⟨1, rfl⟩

end Representation.QuadraticFourGroup

end
