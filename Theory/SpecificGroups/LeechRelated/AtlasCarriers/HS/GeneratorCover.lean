module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS

/-!
# Generation from the published HS permutations

The two specified permutations generate the exact ATLAS carrier by its
construction. Transporting them across an actual multiplicative equivalence
therefore tests containment of an embedded copy of that carrier. If adjoining
`T` to this copy gives the ambient group, any subgroup family covering `T` and
the two transported generators generates the ambient group as well.

These are closure and transport lemmas, not order, simplicity, local-structure,
or E-generation assertions for HS. The permutation data and their provenance
are in `Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS`.
-/

@[expose] public section

namespace Sporadic.LeechRelated.HS
open Subgroup

/-- The first published generator, as an element of the generated carrier. -/
def generatorAElement : Carrier := ⟨generatorA, subset_closure (by simp)⟩
/-- The second published generator, as an element of the generated carrier. -/
def generatorBElement : Carrier := ⟨generatorB, subset_closure (by simp)⟩

/-- A subgroup containing both published generators is the whole carrier. -/
theorem eq_top_of_generators_mem (H : Subgroup Carrier)
    (ha : generatorAElement ∈ H) (hb : generatorBElement ∈ H) :
    H = ⊤ := by
  have h : generated ≤ H.map inclusion := by
    apply (closure_le _).mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · rw [hx]
      exact ⟨generatorAElement, ha, rfl⟩
    · rw [Set.mem_singleton_iff.mp hx]
      exact ⟨generatorBElement, hb, rfl⟩
  apply top_unique
  intro x _
  obtain ⟨y, hy, he⟩ := h x.property
  exact inclusion_injective he ▸ hy

variable {G : Type*} [Group G]

/-- Test containment of an isomorphic embedded carrier on the two generators. -/
theorem le_of_generators_mem (L M : Subgroup G) (e : L ≃* Carrier)
    (ha : (e.symm generatorAElement : G) ∈ M)
    (hb : (e.symm generatorBElement : G) ∈ M) : L ≤ M := by
  let f := L.subtype.comp e.symm.toMonoidHom
  have h : M.comap f = ⊤ := eq_top_of_generators_mem _ ha hb
  intro x hx
  have hm : e ⟨x, hx⟩ ∈ M.comap f := h ▸ mem_top _
  simpa only [mem_comap, f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply, Subgroup.subtype_apply] using hm

/-- Generator coverage, together with a supplement, proves family generation. -/
theorem sSup_eq_top_of_generators_mem (L T : Subgroup G) (e : L ≃* Carrier)
    (hLT : L ⊔ T = ⊤) (Δ : Set (Subgroup G))
    (hT : T ≤ sSup Δ)
    (ha : (e.symm generatorAElement : G) ∈ sSup Δ)
    (hb : (e.symm generatorBElement : G) ∈ sSup Δ) :
    sSup Δ = ⊤ := by
  apply top_unique
  rw [← hLT]
  exact sup_le (le_of_generators_mem L _ e ha hb) hT

end Sporadic.LeechRelated.HS
