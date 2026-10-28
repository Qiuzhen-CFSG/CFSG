module

public import Theory.AlgebraicGroup.RootSubgroups.ReductiveCharacterRootGeometry
public import Theory.AlgebraicGroup.RootSubgroups.ReductiveIntegralCoroots.Realization

/-!
# From actual root support and rank-one reflections to complete root data

The proportional-root exclusion and the actual rank-one conjugation equations
construct the real geometry of the root lattice. The same algebraic
cocharacters supply integral functionals on the whole character lattice.
Applying the existing realization theorem then gives actual root subgroups,
complete addition, a positive system, and nonzero integral heights.

This is a conditional application of GLS3, Theorem 1.9.5(d). The source
support assertions in Borel §13.18 and existence of rank-one reflections must
still be proved from reductivity by the geometric assembly owner.
-/

universe u
namespace Theory.AlgebraicGroup
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G] {T : ClosedSubgroup G}

/-- The geometric construction feeds the literal root-data consumer, using
the same actual torus characters and rank-one algebraic cocharacters. -/
public theorem exists_complete_rootGroupData_of_rankOne_reflections_of_root_support
    (hT : IsMaximalTorus T)
    (hne : ∀ α : TorusRootIndex T, α.val ≠ 1)
    (hneg : ∀ α : TorusRootIndex T, IsTorusRoot T α.val⁻¹)
    (hred : ∀ α β : TorusRootIndex T, ∀ m : ℤ,
      α.val ^ (2 : ℤ) = β.val ^ m → α.val = β.val ∨ α.val = β.val⁻¹)
    (h : ∀ χ : TorusWeight T, χ ≠ 1 → IsTorusRoot T χ →
      IsTorusRoot T χ⁻¹ → Nonempty (IntegralCorootReflection T χ)) :
    ∃ D : RootGroupData G T, D.IsRealization ∧ D.IsRootAdditionComplete ∧
      IsPositiveSystem D D.positive ∧ ∀ α, D.height α ≠ 0 := by
  obtain ⟨R⟩ :=
    exists_torusCharacterRootGeometry_of_rankOne_reflections_of_root_support
      hT hne hneg hred h
  exact exists_complete_rootGroupData_of_rankOne_reflections hT R h

end Theory.AlgebraicGroup
