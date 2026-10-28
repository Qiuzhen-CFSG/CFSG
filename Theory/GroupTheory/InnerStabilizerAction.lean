module

public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Inner action of an automorphism stabilizer

For a subgroup A of G, the intrinsic assertion below says that every
automorphism of G preserving A restricts to conjugation by an element of A.
It refers to the actual inclusion of A in G. Transport along an ambient
isomorphism carries both the subgroup and its automorphisms together.

Source application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript of 1 March 2004, proof of Lemma 1.3.9, printed p.514.
-/

@[expose] public section
namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

/-- Every ambient automorphism stabilizing A acts on A by an inner automorphism. -/
def HasInnerStabilizerAction (A : Subgroup G) : Prop :=
  ∀ α : MulAut G, A.map α.toMonoidHom = A →
    ∃ a ∈ A, ∀ x ∈ A, α x = a * x * a⁻¹

/-- Transport the stabilizer assertion from the image of the actual subgroup. -/
theorem HasInnerStabilizerAction.of_map {A : Subgroup G} (e : G ≃* H)
    (h : HasInnerStabilizerAction (A.map e.toMonoidHom)) :
    HasInnerStabilizerAction A := by
  intro α hα
  let β : MulAut H := e.symm.trans (α.trans e)
  have hc : β.toMonoidHom.comp e.toMonoidHom = e.toMonoidHom.comp α.toMonoidHom := by
    ext x
    simp [β]
  have hβ : (A.map e.toMonoidHom).map β.toMonoidHom = A.map e.toMonoidHom := by
    rw [map_map, hc, ← map_map, hα]
  obtain ⟨a, ⟨b, hb, rfl⟩, ha⟩ := h β hβ
  refine ⟨b, hb, fun x hx => e.injective ?_⟩
  simpa [β] using ha (e x) (mem_map_of_mem e.toMonoidHom hx)

end Subgroup
