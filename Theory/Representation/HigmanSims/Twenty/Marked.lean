module

public import Theory.Representation.HigmanSims.Twenty.Generators
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# The marked comparison required by the HS degree-twenty model

A comparison must send the two literal degree-100 generators to the two
literal degree-twenty matrices. Generation proves its surjectivity. Given
the simplicity inherited by the chapter consumer, the nontrivial matrix
word `ab` proves injectivity, and hence an actual carrier isomorphism.
No marked homomorphism is constructed in this module.

The permutation generators invert the published right permutations, whereas
the matrices keep the published rows. This preserves products: inversion
turns composition of right permutations into Lean's left composition.
The two representations must be compared with precisely these conventions.

Source: ATLAS HSG1-p100B0 and HSG1-f2r20B0.
-/

@[expose] public section
namespace Sporadic.LeechRelated.HS.Twenty

def permutationA : HS.Carrier :=
  ⟨HS.generatorA, Subgroup.subset_closure (by simp)⟩

def permutationB : HS.Carrier :=
  ⟨HS.generatorB, Subgroup.subset_closure (by simp)⟩

/-- Required generator marking; existence remains a separate construction. -/
structure MarkedComparison where
  hom : HS.Carrier →* MatrixCarrier
  map_a : hom permutationA = a
  map_b : hom permutationB = b

namespace MarkedComparison

variable (C : MarkedComparison)

theorem surjective : Function.Surjective C.hom := by
  let f : HS.Carrier →* Ambient := matrixGroup.subtype.comp C.hom
  have hr : matrixGroup ≤ f.range := by
    change Subgroup.closure {generatorA, generatorB} ≤ f.range
    rw [Subgroup.closure_le]
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact ⟨permutationA, congrArg Subtype.val C.map_a⟩
    · have he : x = generatorB := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨permutationB, congrArg Subtype.val C.map_b⟩
  intro x
  obtain ⟨g, hg⟩ := hr x.property
  exact ⟨g, Subtype.ext hg⟩

theorem injective [IsSimpleGroup HS.Carrier] : Function.Injective C.hom := by
  rcases Subgroup.Normal.eq_bot_or_eq_top (inferInstance : C.hom.ker.Normal) with h | h
  · exact C.hom.ker_eq_bot_iff.mp h
  · have hm : C.hom (permutationA * permutationB) = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [h]
      trivial
    rw [map_mul, C.map_a, C.map_b, ← eleven] at hm
    have ho := orderOf_eq_one_iff.mpr hm
    rw [eleven_order] at ho
    contradiction

/-- A proved comparison is an isomorphism, using source-inherited simplicity. -/
noncomputable def equiv [IsSimpleGroup HS.Carrier] : HS.Carrier ≃* MatrixCarrier :=
  MulEquiv.ofBijective C.hom ⟨C.injective, C.surjective⟩

def action : Representation (ZMod 2) HS.Carrier Vector := representation.comp C.hom

theorem action_injective [IsSimpleGroup HS.Carrier] : Function.Injective C.action :=
  representation_injective.comp C.injective

theorem action_finrank : Module.finrank (ZMod 2) Vector = 20 := representation_finrank

theorem map_eleven : C.hom (permutationA * permutationB) = eleven := by
  rw [map_mul, C.map_a, C.map_b]
  rfl

theorem action_eleven_fixedFree :
    LinearMap.ker (C.action (permutationA * permutationB) - 1) = ⊥ := by
  change LinearMap.ker (representation (C.hom (permutationA * permutationB)) - 1) = ⊥
  rw [C.map_eleven]
  exact eleven_fixedFree

end MarkedComparison
end Sporadic.LeechRelated.HS.Twenty
