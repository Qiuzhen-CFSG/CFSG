module

public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.Basic
public import Mathlib.Algebra.Group.Subgroup.Ker

/-!+# The max3 words for the Thompson involution centralizer

These are the two outputs of the ATLAS program `ThG1-max3W1`, evaluated in
the fixed matrix carrier. The original register program and its provenance
are in `source/`. The generated subgroup is defined independently of any
claim about its order, centralization or alternating quotient.

The intermediate expressions retain the source multiplication convention.
The matrix certification must prove both word images and centralization;
the source description of the subgroup is not assumed here.
-/

namespace Thompson.InvolutionCentralizer.AlternatingQuotient

@[expose] public def seed3 : Model := generatorA * generatorB
@[expose] public def seed4 : Model := seed3 * generatorB
@[expose] public def seed5 : Model := seed3 * seed4
@[expose] public def seed6 : Model := seed3 * seed5
@[expose] public def seed10 : Model := (seed3 * (seed6 * seed5)) * seed4

/-- Output register 1 of `ThG1-max3W1`. -/
@[expose] public def wordA : Model :=
  ((seed10 * generatorA)⁻¹ * (generatorA * seed10)) ^ 14

/-- Output register 2 of `ThG1-max3W1`. -/
@[expose] public def wordB : Model :=
  (generatorA * seed6) * ((seed6 * generatorA)⁻¹ * (generatorA * seed6)) ^ 9

/-- The subgroup whose four-space action will supply the alternating quotient. -/
@[expose] public def wordSubgroup : Subgroup Model :=
  Subgroup.closure {wordA, wordB}

public theorem wordA_mem : wordA ∈ wordSubgroup :=
  Subgroup.subset_closure (Set.mem_insert _ _)

public theorem wordB_mem : wordB ∈ wordSubgroup :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

@[expose] public def generatorX : wordSubgroup := ⟨wordA, wordA_mem⟩
@[expose] public def generatorY : wordSubgroup := ⟨wordB, wordB_mem⟩

/-- The literal source words generate the subgroup carrier. -/
public theorem generators_closure : Subgroup.closure {generatorX, generatorY} = ⊤ := by
  apply Subgroup.map_injective wordSubgroup.subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
    Set.image_pair]
  rfl

end Thompson.InvolutionCentralizer.AlternatingQuotient
