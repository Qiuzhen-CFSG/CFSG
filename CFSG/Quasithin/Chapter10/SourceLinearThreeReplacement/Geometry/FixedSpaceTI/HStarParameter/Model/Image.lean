module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.Model.Parameter
public import Theory.Representation.BinaryPermutation.FiveWreathSimple

/-!
# Actual subrepresentations from nonzero wreath model maps

Simplicity makes a nonzero model map injective. Its literal range, with the
restricted original representation, inherits faithfulness and the parameter
bound through the induced equivariant linear equivalence. This keeps the
required constituent inside the original module.

Source: Aschbacher--Smith 10.3.1, printed pp.755--756.
-/

@[expose] public section

open Representation
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.Model
open ChapterE

theorem faithful_bounded_subrepresentation_of_injective
    {X U V : Type*} [Group X] [AddCommGroup U] [Module (ZMod 2) U]
    [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) X U) (ρ : Representation (ZMod 2) X V)
    (hσ : Function.Injective σ) (ha : moduleA σ ≤ 1)
    (f : σ.IntertwiningMap ρ) (hf : Function.Injective f) :
    ∃ S : Subrepresentation ρ,
      Function.Injective S.toRepresentation ∧ moduleA S.toRepresentation ≤ 1 := by
  let E : U ≃ₗ[ZMod 2] f.range.toSubmodule := LinearEquiv.ofInjective f.toLinearMap hf
  have hE (g : X) (u : U) : E (σ g u) = f.range.toRepresentation g (E u) := by
    apply Subtype.ext
    exact IntertwiningMap.isIntertwining σ ρ f g u
  refine ⟨f.range, ?_, ?_⟩
  · intro a b hab
    apply hσ
    apply LinearMap.ext
    intro u
    apply E.injective
    rw [hE, hE, hab]
  · have he := moduleA_eq_of_equivariant_equiv σ f.range.toRepresentation
      (MulEquiv.refl X) E hE
    exact he ▸ ha

open BinaryPermutation BinaryPermutation.FiveTensorSquare

theorem faithful_bounded_subrepresentation_of_nonzero_model_map
    {X V : Type*} [Group X] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) X V) (e : X ≃* Wreath)
    (h : (∃ f : IntertwiningMap (FivePair.wreathRepresentation.comp e.toMonoidHom) ρ, f ≠ 0) ∨
      ∃ f : IntertwiningMap (tensorWreathAction.comp e.toMonoidHom) ρ, f ≠ 0) :
    ∃ S : Subrepresentation ρ,
      Function.Injective S.toRepresentation ∧ moduleA S.toRepresentation ≤ 1 := by
  rcases h with ⟨f,hf⟩ | ⟨f,hf⟩
  · let : IsIrreducible (FivePair.wreathRepresentation.comp e.toMonoidHom) :=
      RepEquiv.irreducible_of_group_iso (ρ := FivePair.wreathRepresentation) e.symm
        (fun g v => by simp) pairWreathAction_irreducible
    exact faithful_bounded_subrepresentation_of_injective _ ρ
      (FivePair.wreathRepresentation_injective.comp e.injective)
      ((moduleA_comp_le _ _ e.injective).trans pair_moduleA_le_one) f
      ((IsIrreducible.injective_or_eq_zero f).resolve_right hf)
  · let : IsIrreducible (tensorWreathAction.comp e.toMonoidHom) :=
      RepEquiv.irreducible_of_group_iso (ρ := tensorWreathAction) e.symm
        (fun g v => by simp) tensorWreathAction_irreducible
    exact faithful_bounded_subrepresentation_of_injective _ ρ
      (tensorWreathAction_injective.comp e.injective)
      ((moduleA_comp_le _ _ e.injective).trans tensor_moduleA_le_one) f
      ((IsIrreducible.injective_or_eq_zero f).resolve_right hf)
end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.Model
