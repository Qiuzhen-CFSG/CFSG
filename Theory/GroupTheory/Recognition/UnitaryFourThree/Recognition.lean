module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.LocalComparison
public import Theory.GroupTheory.Recognition.UnitaryFourThree.NativeModel.IsType
/-!
# Recognition of the original type U₄(3)

Any two finite groups satisfying the unchanged Asc94 IsType definition
have isomorphic original cubic geometries and hence are isomorphic.
The literal field-nine projective special unitary group satisfies IsType,
so the conclusion identifies the actual native matrix carrier.
Source: Aschbacher, Sporadic Groups (1994),45.11, pp.248–249.
-/
public section
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
variable {G : Type*} [Group G] [Finite G] {z : G} (h : IsType z)
variable {G' : Type*} [Group G'] [Finite G'] {z' : G'} (h' : IsType z')
include h h' in
theorem equiv : Nonempty (G≃*G') := by
  obtain ⟨c⟩ := h.original_cubic_source_configuration (Sylow.nonempty.some)
  obtain ⟨c'⟩ := h'.original_cubic_source_configuration (Sylow.nonempty.some)
  exact c.exists_group_equiv c'

include h in
theorem equiv_native : Nonempty (G≃*Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.Carrier 4) :=
  h.equiv Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.SourceType.native_isType
end Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
