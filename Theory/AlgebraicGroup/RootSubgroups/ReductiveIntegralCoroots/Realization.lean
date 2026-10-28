module

public import Theory.AlgebraicGroup.RootSubgroups.ReductiveIntegralCoroots
public import Theory.AlgebraicGroup.RootSubgroups.ReductiveRealization

/-!
# Applying rank-one reflections to the actual root-data constructor

The rank-one torus-conjugation input supplies integral functionals on all
characters. This module applies them to the existing constructor, including
its algebraic cocharacters and every weight--cocharacter equation. The local
geometric existence premise stays explicit until its producer is complete.

Source: GLS3, Theorem 1.9.5(d) and Remarks 1.9.6.
-/

universe u
namespace Theory.AlgebraicGroup
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G] {T : ClosedSubgroup G}

/-- Actual root geometry and rank-one torus reflections give complete actual
root data. This is conditional on constructing the rank-one geometric input. -/
public theorem exists_complete_rootGroupData_of_rankOne_reflections
    (hT : IsMaximalTorus T) (R : TorusCharacterRootGeometry T)
    (h : ∀ χ : TorusWeight T, χ ≠ 1 → IsTorusRoot T χ →
      IsTorusRoot T χ⁻¹ → Nonempty (IntegralCorootReflection T χ)) :
    ∃ D : RootGroupData G T, D.IsRealization ∧ D.IsRootAdditionComplete ∧
      IsPositiveSystem D D.positive ∧ ∀ α, D.height α ≠ 0 :=
  exists_complete_rootGroupData_of_characterRootGeometry hT.1 R
    (R.hasIntegralCoroots_of_rankOne_reflections h)

end Theory.AlgebraicGroup
