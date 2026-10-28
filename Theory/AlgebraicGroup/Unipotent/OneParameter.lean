module

public import Theory.AlgebraicGroup.Unipotent.OneParameterCore

/-!
GLS3 Theorem 1.3.5(c), isolated from the proved one-parameter infrastructure in
`OneParameterCore`. The forward implication follows from an additive-group
parametrization. The converse classification of connected one-dimensional
unipotent groups is the remaining result.
-/

universe u

namespace Theory.AlgebraicGroup

set_option warningAsError false in
public theorem theorem_1_3_5_c
    {k : Type u} [Field k] [IsAlgClosed k]
    {Y : Variety k} [AlgebraicGroup Y] :
    IsOneParameterGroup Y ↔
      Variety.IsConnected Y ∧ Variety.dimension Y = 1 ∧
        IsUnipotentAlgebraicGroup Y := by
  constructor
  · intro hY
    exact ⟨hY.isConnected, hY.dimension_eq_one,
      hY.isUnipotentAlgebraicGroup⟩
  · intro hY
    sorry

end Theory.AlgebraicGroup
