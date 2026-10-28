module
public import Theory.GroupAction.PermutationSection
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi24Prime
public import Mathlib.GroupTheory.OrderOfElement
/-!
# A Fi22 section from the actual Fi24 permutation lifts

Two elements centralizing an involution and inducing the literal Fi22
generators on an injectively labelled set of 3510 letters generate a subgroup
with a surjective map to the actual Fi22 carrier. The pair-subgroup argument
requires no description of the centralizer outside these letters.

This is the final algebraic assembly for the concrete source certificates in
Aschbacher--Smith A.2.19, pp.40--41, and GLS3 Table 5.3u.
-/

@[expose] public noncomputable section
namespace Sporadic.Fischer.Fi24Prime.CentralizerSection
open Subgroup

theorem exists_source_section_of_lifts
    (t u v : Carrier) (ht : orderOf t = 2)
    (hu : u ∈ centralizer ({t} : Set Carrier))
    (hv : v ∈ centralizer ({t} : Set Carrier))
    (point : Fin 3510 → Fin 306936) (hp : Function.Injective point)
    (ha : ∀ y, inclusion u (point y) = point (Fi22.generatorA y))
    (hb : ∀ y, inclusion v (point y) = point (Fi22.generatorB y)) :
    ∃ (s : Carrier) (L : Subgroup Carrier) (f : L →* Fi22.Carrier),
      orderOf s = 2 ∧ L ≤ centralizer ({s} : Set Carrier) ∧
      Function.Surjective f := by
  let a : Fi22.Carrier := ⟨Fi22.generatorA, subset_closure (by simp)⟩
  let b : Fi22.Carrier := ⟨Fi22.generatorB, subset_closure (by simp)⟩
  have hg : closure ({a,b} : Set Fi22.Carrier) = ⊤ := by
    have he : ({a,b} : Set Fi22.Carrier) =
        Fi22.generated.subtype ⁻¹' ({Fi22.generatorA,Fi22.generatorB} : Set _) := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro (rfl | rfl) <;> simp [a,b]
      · rintro (h | h)
        · exact Or.inl (Subtype.ext h)
        · exact Or.inr (Subtype.ext h)
    rw [he]
    exact closure_preimage_eq_top _
  obtain ⟨L,f,hL,hf⟩ := Theory.GroupAction.PermutationSection.exists_section_of_generators
    inclusion Fi22.inclusion Fi22.inclusion_injective point hp u v a b hg ha hb
    (centralizer ({t} : Set Carrier)) hu hv
  exact ⟨t,L,f,ht,hL,hf⟩
end Sporadic.Fischer.Fi24Prime.CentralizerSection
