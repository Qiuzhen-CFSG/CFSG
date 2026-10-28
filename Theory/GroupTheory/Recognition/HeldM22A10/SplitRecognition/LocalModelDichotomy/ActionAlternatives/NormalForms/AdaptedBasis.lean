module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.Coordinates

/-!
# The basis adapted to Janko's cubic and reflection

The preliminary basis in Janko, *A characterization of the Mathieu simple
groups, I*, J. Algebra 9 (1968), Section 1, printed p.2, has its first two
vectors in the fixed space of the cubic and its last two in the moved space.
The first vector is fixed by the whole actor. The reflection has one binary
parameter on the fixed plane. `JankoAdaptedBasis` records this preliminary
construction, before the action of `a` has been determined.

The parameter matrices below transcribe the two displayed rows of the source.
As in `JankoCoordinates`, the cubic formula describes the action of `c⁻¹`.
This module does not assert existence of the preliminary basis.
-/

namespace Theory.GroupTheory.HeldM22A10.LocalModelDichotomy

/-- A coordinate vector, in multiplicative notation. -/
@[expose] public def jankoUnit (i : Fin 4) : BinaryFour :=
  Multiplicative.ofAdd (Pi.single i 1)

/-- The reflection matrix before its binary parameter has been determined. -/
@[expose] public def jankoParameterD (α : ZMod 2) (v : BinaryFour) : BinaryFour :=
  let x := v.toAdd
  Multiplicative.ofAdd ![x 0 + α * x 1, x 1, x 2 + x 3, x 3]

/-- The source's four-parameter matrix for right conjugation by `a`. -/
@[expose] public def jankoParameterA (α β γ δ : ZMod 2) (v : BinaryFour) : BinaryFour :=
  let x := v.toAdd
  Multiplicative.ofAdd ![x 0 + β * γ * x 1 + α * δ * x 2 + γ * x 3,
    x 1 + δ * x 3, x 2 + β * x 1, x 3]

/-- The initial source basis, with the cubic and reflection normalized.
The remaining double transposition is only required to fix the first vector. -/
public structure JankoAdaptedBasis (ρ : SymmetricFour →* MulAut BinaryFour) where
  basis : BinaryFour ≃* BinaryFour
  alpha : ZMod 2
  action_c : ∀ v, ρ jankoC⁻¹ (basis v) = basis (jankoSourceC v)
  action_d : ∀ v, ρ jankoD (basis v) = basis (jankoParameterD alpha v)
  fixed_a : ρ jankoA (basis (jankoUnit 0)) = basis (jankoUnit 0)

end Theory.GroupTheory.HeldM22A10.LocalModelDichotomy
