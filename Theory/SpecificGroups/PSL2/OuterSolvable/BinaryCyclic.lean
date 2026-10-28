module

public import Theory.SpecificGroups.PSL2.OuterSolvable.Actions
public import Theory.SpecificGroups.PSL2.OuterSolvable.FieldAutomorphisms
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Cyclic binary PSL₂ outer quotient from semilinear coverage

The field automorphisms map onto the actual quotient by inner automorphisms
when inner-field coverage holds. Their cyclicity therefore gives cyclicity
of the outer quotient, without choosing semilinear representatives.

Source: GLS3, Theorem 2.5.12, the characteristic-two A₁ case.
-/

namespace Theory.PSL2.OuterSolvable

/-- Inner-field coverage makes the actual binary PSL₂ outer group cyclic. -/
public theorem outer_isCyclic_of_field_coverage
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hcoverage : ∀ a : MulAut (Group F), ∃ (g : Group F) (σ : F ≃+* F),
      a = MulAut.conj g * fieldAut σ) :
    IsCyclic (MulAut.Outer (Group F)) := by
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (Group F))
  let f := q.comp (projectiveFieldAutHom (K := F))
  let : IsCyclic (F ≃+* F) := finiteFieldAut_isCyclic
  apply isCyclic_of_surjective f
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup (Group F)) x
  obtain ⟨g, σ, ha⟩ := hcoverage a
  refine ⟨σ, ?_⟩
  have hg : q (MulAut.conj g) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩
  change q (projectiveFieldAutHom σ) = q a
  rw [projectiveFieldAutHom_eq_fieldAut, ha, map_mul, hg, one_mul]

end Theory.PSL2.OuterSolvable
