module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Transporting involution-centralizer sections through embeddings

An injective homomorphism carries a subgroup of an involution centralizer
to a subgroup of the image involution's centralizer. Transport a surjective
homomorphism across the isomorphism from the numerator to its image; its
kernel remains a p-group. No ambient normality or splitting is required.

This elementary transport is used in the Fi₂₃ subgroup route to the
Fi₂₄′ local section in GLS3, Table 5.3v and its explanatory paragraph.
-/

public section

namespace Theory.GroupTheory

open Subgroup

/-- An involution-centralizer section with p-group kernel survives an
embedding of the ambient group. -/
theorem exists_involutionCentralizer_section_of_injective
    {H G S : Type*} [Group H] [Group G] [Group S]
    (e : H →* G) (he : Function.Injective e)
    (t : H) (ht : orderOf t = 2)
    (L : Subgroup H) (hL : L ≤ centralizer ({t} : Set H))
    (f : L →* S) (hf : Function.Surjective f)
    (p : ℕ) (hk : IsPGroup p f.ker) :
    ∃ (u : G) (M : Subgroup G) (g : M →* S),
      orderOf u = 2 ∧ M ≤ centralizer ({u} : Set G) ∧
      Function.Surjective g ∧ IsPGroup p g.ker := by
  let j : L ≃* L.map e := L.equivMapOfInjective e he
  let g : L.map e →* S := f.comp j.symm.toMonoidHom
  refine ⟨e t, L.map e, g, (orderOf_injective e he t).trans ht, ?_, ?_, ?_⟩
  · simpa only [Set.image_singleton] using
      (Subgroup.map_mono hL).trans (map_centralizer_le_centralizer_image _ e)
  · exact hf.comp j.symm.surjective
  · change IsPGroup p (f.ker.comap j.symm.toMonoidHom)
    exact hk.comap_of_injective j.symm.toMonoidHom j.symm.injective

end Theory.GroupTheory
