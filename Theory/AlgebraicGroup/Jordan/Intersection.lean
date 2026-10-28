module

public import Theory.AlgebraicGroup.Jordan.Components

universe u

/-! Intersection of semisimple and unipotent elements. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- An algebraic-group element which is both semisimple and unipotent is the
identity. -/
public theorem semisimple_unipotent_eq_one
    {G : Variety k} [AlgebraicGroup G] (x : Variety.Point G)
    (hs : IsSemisimpleElement G x) (hu : IsUnipotentElement G x) :
    x = 1 := by
  let semisimpleDecomposition : JordanDecomposition x :=
    { semisimplePart := x
      unipotentPart := 1
      eq_mul := by simp
      commute := Commute.one_right x
      semisimple := hs
      unipotent := one_isUnipotentElement G }
  let unipotentDecomposition : JordanDecomposition x :=
    { semisimplePart := 1
      unipotentPart := x
      eq_mul := by simp
      commute := Commute.one_left x
      semisimple := one_isSemisimpleElement G
      unipotent := hu }
  have h := semisimpleDecomposition.unique unipotentDecomposition
  exact congrArg JordanDecomposition.semisimplePart h

/-- An algebraic-group element is both semisimple and unipotent exactly when
it is the identity. -/
public theorem semisimple_unipotent_iff_eq_one
    {G : Variety k} [AlgebraicGroup G] (x : Variety.Point G) :
    IsSemisimpleElement G x ∧ IsUnipotentElement G x ↔ x = 1 := by
  constructor
  · rintro ⟨hs, hu⟩
    exact semisimple_unipotent_eq_one x hs hu
  · rintro rfl
    exact ⟨one_isSemisimpleElement G, one_isUnipotentElement G⟩

end Theory.AlgebraicGroup
