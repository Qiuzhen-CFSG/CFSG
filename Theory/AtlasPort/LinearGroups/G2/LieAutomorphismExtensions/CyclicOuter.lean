module
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage
public import Theory.SpecificGroups.PSL2.OuterSolvable.FieldAutomorphisms
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# The cyclic outer quotient of the binary G2 model

Actual inner-field coverage makes the field-automorphism map onto the outer
quotient. The finite field automorphism group is cyclic, so its image is cyclic.
This is the outer-action input of Aschbacher--Smith 13.6.6, printed p.927.
-/

public section
open Subgroup Theory.GroupTheory
namespace Atlas.G2.LieAutomorphismExtensions
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
theorem outer_isCyclic (hq : 2 < Nat.card F) : IsCyclic (MulAut.Outer (Model F)) := by
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (Model F))
  let f := q.comp (fieldAction (F := F))
  let : IsCyclic (F ≃+* F) := Theory.PSL2.OuterSolvable.finiteFieldAut_isCyclic
  apply isCyclic_of_surjective f
  intro x
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup (Model F)) x
  obtain ⟨g,σ,rfl⟩ := exists_inner_field hq a
  refine ⟨σ, ?_⟩
  change q (fieldAction σ) = q (MulAut.conj g * fieldAction σ)
  have hg : q (MulAut.conj g) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨g,rfl⟩
  rw [map_mul,hg,one_mul]
end Atlas.G2.LieAutomorphismExtensions

