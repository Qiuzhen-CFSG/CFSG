module
public import Theory.Representation.BinaryLinearNormalizerResidual
public import Theory.Representation.SL5ExteriorSquare.MarkedRecognition

/-!
# Normal binary linear actors fill a faithful overgroup

A normal subgroup's action image is normalized by the entire ambient action.
For the binary natural module this image is the full general linear group;
for an irreducible ten-dimensional SL₅(2) module its image is self-normalizing.
Faithfulness therefore makes the normal subgroup the entire ambient group.
Both statements retain the actual action and the marked group isomorphism.

Source application: Aschbacher--Smith 10.2.9, printed pp.751--752, using the
natural and exterior rows of B.4.2, printed pp.85--86.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped MatrixGroups

namespace Representation.BinaryLinearNormalActors
open BinaryNormalizerResidual BinaryLinearNormalizerResidual

private theorem eq_top_of_self_normalizing_image
    {Q V : Type*} [Group Q] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) Q V) (hf : Function.Injective ρ)
    (A : Subgroup Q) [A.Normal]
    (hn : linearNormalizer (ρ.comp A.subtype) = actionImage (ρ.comp A.subtype)) : A = ⊤ := by
  have hr : actionImage (ρ.comp A.subtype) = A.map ρ.asGroupHom := by
    have he : Representation.asGroupHom (ρ.comp A.subtype) = ρ.asGroupHom.comp A.subtype := by
      apply MonoidHom.ext
      intro g
      apply Units.ext
      rfl
    rw [actionImage,he,MonoidHom.range_comp,range_subtype]
  change normalizer (actionImage (ρ.comp A.subtype) : Set (Module.End (ZMod 2) V)ˣ) = _ at hn
  rw [hr] at hn
  apply top_unique
  intro x _
  have hx : ρ.asGroupHom x ∈ normalizer (A.map ρ.asGroupHom : Set _) :=
    A.le_normalizer_map ρ.asGroupHom
      (mem_map_of_mem _ (by rw [A.normalizer_eq_top]; trivial))
  rw [hn] at hx
  obtain ⟨a,ha,he⟩ := hx
  exact hf (congrArg Units.val he) ▸ ha

/-- A normal subgroup acting as the full binary natural linear group is the whole faithful actor. -/
theorem normal_natural_eq_top
    {Q V : Type*} [Group Q] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) Q V) (hf : Function.Injective ρ)
    (A : Subgroup Q) [A.Normal] (n : ℕ)
    (e : A ≃* SL(n,ZMod 2)) (E : V ≃ₗ[ZMod 2] (Fin n → ZMod 2))
    (hE : ∀ (a : A) v, E (ρ a v) = specialLinearNatural n (e a) (E v)) : A = ⊤ := by
  apply eq_top_of_self_normalizing_image ρ hf A
  apply normalizer_eq_of_equiv (ρ.comp A.subtype) (specialLinearNatural (k := ZMod 2) n) e E hE
  simp only [linearNormalizer,natural_image_eq_top,normalizer_eq_top]

/-- A normal SL₅(2) acting irreducibly in dimension ten is the whole faithful actor. -/
theorem normal_ten_dimensional_eq_top
    {Q V : Type*} [Group Q] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) Q V) (hf : Function.Injective ρ)
    (A : Subgroup Q) [A.Normal] [IsIrreducible (ρ.comp A.subtype)]
    (e : A ≃* SL(5,ZMod 2)) (hd : Module.finrank (ZMod 2) V = 10) : A = ⊤ := by
  obtain ⟨a,E,_,hE⟩ := SL5ExteriorSquare.square_coordinates_of_finrank_ten
    (ρ.comp A.subtype) e hd
  exact eq_top_of_self_normalizing_image ρ hf A
    (normalizer_eq_of_equiv (ρ.comp A.subtype) _ a E hE
      SL5TenDimensional.ExteriorNormalizer.normalizer_two)

end Representation.BinaryLinearNormalActors
